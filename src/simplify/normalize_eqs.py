"""Normalize equalities-to-zero to their primitive (content-divided) form.

Motivation: two field-equivalent constraints can reach the solver with a linear
factor scaled by a field unit on one side and divided out on the other — e.g. a
hypothesis ``(= (mod (+ 125829120 (* 2005401601 w) (* 7864320 a)) p) 0)`` versus a
goal ``(= (mod (+ 16 a (* (- 1) w)) p) 0)`` (the same factor divided by 7864320).
z3's *core* preprocessing gcd-normalizes the standalone (goal) atoms but leaves
equalities buried inside an ``or`` (the hypothesis choice-splits) alone, so the
solver must re-derive ``c·X ≡ 0 ⟹ X ≡ 0`` per row — pure LIA GCD/Diophantine work.

This pass does that normalization *uniformly* and at every polarity (it walks into
``or``/``and``/``not``), independent of z3's version-specific preprocessing: for each
``(= (mod t m) 0)`` atom it divides ``t`` by the gcd of its (symmetrized) integer
coefficients when that gcd is coprime to ``m`` (so it is a unit mod ``m``, making the
division truth-preserving under ``≡ 0``). Plain ``(= t 0)`` integer equalities are
handled too (content-division is sound in an integral domain, no coprime guard).

The division is sound *only* in the ``≡ 0`` / ``≢ 0`` context, which is exactly what
this pass matches — it never touches a ``mod`` used as a value (inside ``<`` or
mod-inv), so the soundness boundary is structural.
"""
import math

from pysmt.walkers import IdentityDagWalker

from ..smt.utils import *


def _term_coeff_and_monomial(term: FNode) -> tuple[int, FNode | None]:
    """Split an additive term into ``(integer_coeff, monomial)``; monomial ``None`` = constant."""
    if term.is_int_constant():
        return int(term.constant_value()), None
    if term.is_times():
        coeff = 1
        rest = []
        for f in term.args():
            if f.is_int_constant():
                coeff *= int(f.constant_value())
            else:
                rest.append(f)
        if not rest:
            return coeff, None
        return coeff, rest[0] if len(rest) == 1 else Times(*rest)
    # bare symbol or other non-constant monomial: implicit coefficient 1
    return 1, term


def _content_divide(expr: FNode, modulus: int | None) -> FNode | None:
    """Divide ``expr`` by the gcd of its (symmetrized) integer coefficients.

    ``modulus`` set: the equality is ``expr ≡ 0 (mod modulus)``; only divide by a
    gcd coprime to ``modulus`` (a field unit). ``modulus`` None: plain integer
    ``expr = 0``; any gcd > 1 is sound. Returns the divided expression, or ``None``
    when there is nothing to do.
    """
    terms = list(expr.args()) if expr.is_plus() else [expr]
    parsed = [_term_coeff_and_monomial(t) for t in terms]

    def symmetrize(c: int) -> int:
        if modulus is None:
            return c
        c %= modulus
        return c - modulus if c > modulus // 2 else c

    coeffs = [symmetrize(c) for c, _ in parsed]
    g = 0
    for c in coeffs:
        g = math.gcd(g, abs(c))
    if g <= 1:
        return None
    if modulus is not None and math.gcd(g, modulus) != 1:
        return None

    new_terms: list[FNode] = []
    for (_, mono), cs in zip(parsed, coeffs):
        nc = cs // g  # exact: g divides every cs by construction
        if mono is None:
            new_terms.append(Int(nc))
        elif nc == 1:
            new_terms.append(mono)
        else:
            new_terms.append(Times(Int(nc), mono))
    return Plus(*new_terms) if len(new_terms) > 1 else new_terms[0]


class _NormalizeEqWalker(IdentityDagWalker):
    """Content-divide every ``(= (mod t m) 0)`` / ``(= t 0)`` atom, at any polarity."""

    def __init__(self, env=None):
        IdentityDagWalker.__init__(self, env=env)
        self.divided = 0

    def walk_equals(self, formula, args, **kwargs):
        lhs, rhs = args
        # Mod(t, m) = 0  (either argument order)
        mod_node = None
        if rhs.is_zero() and lhs.is_mod():
            mod_node = lhs
        elif lhs.is_zero() and rhs.is_mod():
            mod_node = rhs
        if mod_node is not None:
            t, modulus = mod_node.args()
            if modulus.is_int_constant():
                t2 = _content_divide(t, int(modulus.constant_value()))
                if t2 is not None:
                    self.divided += 1
                    return self.mgr.Equals(self.mgr.Mod(t2, modulus), Int(0))
        # plain integer  t = 0  (content-division is sound in an integral domain)
        elif rhs.is_zero() and (lhs.is_plus() or lhs.is_times()):
            t2 = _content_divide(lhs, None)
            if t2 is not None:
                self.divided += 1
                return self.mgr.Equals(t2, Int(0))
        elif lhs.is_zero() and (rhs.is_plus() or rhs.is_times()):
            t2 = _content_divide(rhs, None)
            if t2 is not None:
                self.divided += 1
                return self.mgr.Equals(t2, Int(0))
        return self.mgr.Equals(lhs, rhs)


def simplify_normalize_eqs(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Content-divide every equality-to-zero atom across all assertions."""
    walker = _NormalizeEqWalker(env=get_env())
    asserts_changed = 0
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        old = cmd.args[0]
        new = walker.walk(old)
        if new is not old:
            asserts_changed += 1
        cmd.args[0] = keep_comment(new, old)
    if subaction is not None:
        subaction += {
            "divided_atoms": walker.divided,
            "asserts_changed": asserts_changed,
        }
    return smt_script
