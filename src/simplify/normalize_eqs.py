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


def _rebuild(new_coeffs: list[tuple[int, FNode | None]]) -> FNode:
    """Reassemble ``Σ coeff·monomial`` from ``(coeff, monomial)`` pairs (``None`` = const)."""
    terms: list[FNode] = []
    for nc, mono in new_coeffs:
        if mono is None:
            terms.append(Int(nc))
        elif nc == 0:
            continue  # term vanished
        elif nc == 1:
            terms.append(mono)
        else:
            terms.append(Times(Int(nc), mono))
    if not terms:
        return Int(0)
    return Plus(*terms) if len(terms) > 1 else terms[0]


def _content_divide(expr: FNode, modulus: int | None) -> FNode | None:
    """Divide ``expr`` by the content of its coefficients.

    ``modulus`` None — plain integer ``expr = 0``: integer content-division by the
    gcd of all coefficients (sound in an integral domain).

    ``modulus`` set — ``expr ≡ 0 (mod modulus)``: **field** content-division. The
    content ``g`` is the gcd of the (symmetrized) *linear* coefficients only; every
    coefficient — including the constant — is multiplied by ``g⁻¹ mod modulus`` (a
    field unit, so the equality is preserved) and re-symmetrized. This reaches the
    same primitive form whether the equation arrives scaled by a unit or divided,
    which integer division cannot do: reducing the constant mod ``modulus`` makes it
    coprime to the linear gcd, collapsing the integer gcd to 1.

    Returns the divided expression, or ``None`` when there is nothing to do.
    """
    terms = list(expr.args()) if expr.is_plus() else [expr]
    parsed = [_term_coeff_and_monomial(t) for t in terms]

    if modulus is None:
        coeffs = [c for c, _ in parsed]
        g = 0
        for c in coeffs:
            g = math.gcd(g, abs(c))
        if g <= 1:
            return None
        return _rebuild([(c // g, mono) for (c, mono) in parsed])

    def symmetrize(c: int) -> int:
        c %= modulus
        return c - modulus if c > modulus // 2 else c

    sym = [(symmetrize(c), mono) for c, mono in parsed]
    g = 0
    for c, mono in sym:
        if mono is not None:  # linear coefficients only
            g = math.gcd(g, abs(c))
    if g <= 1 or math.gcd(g, modulus) != 1:
        return None
    gi = pow(g, -1, modulus)
    return _rebuild([(symmetrize((c * gi) % modulus), mono) for (c, mono) in sym])


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
