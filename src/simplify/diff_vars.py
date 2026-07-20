"""Difference-variable substitution.

When the nonlinear (field ``mod``) constraints depend on a pair of ``Int``
columns ``x`` and ``y`` only through their difference ``x - y`` -- the classic
``(x - y)(x - y + c) ≡ 0`` shape produced by limb/permutation checks -- z3's
nlsat has to reason about the quadratic in *two* variables and frequently times
out. Substituting ``x = y + d`` for a fresh ``d`` collapses that quadratic into
one variable: ``y`` cancels out of the degree-2 part entirely, leaving a
polynomial purely in ``d`` that z3 dispatches in milliseconds.

This pass only performs the substitution ``x → y + d`` on the assertions; the
``normalize`` pass that runs after it re-expands the substituted bodies and
cancels ``y`` from the nonlinear part. The change of variables is invertible
(``x = y + d``), so it is sound and equisatisfiable; ``x`` stays declared with a
defining assertion ``x = y + d``, so counterexample models still report it.

Detection is name-agnostic: ``x`` and ``y`` are a difference pair iff, in every
modular equality, the quadratic coefficients satisfy the ``(x - y)²``
signature -- ``coeff(x²) = coeff(y²) = c`` and ``coeff(x·y) = -2c`` (mod p) --
which holds limb-by-limb even when the limbs are cross-multiplied.
"""
import logging

from ..smt.utils import *
from ..utils.args import ARGS
from ..utils.stats import stats_dump
from .normalize import collect_variables, relation_poly_diff, simplify_normalize


def _field_p() -> int:
    return int(ARGS().field_type.value)


def _modular_quadratics(smt_script, var_index, vars_):
    """Per-relation ``{(i,j): coeff}`` (degree-2 monomials) for modular equalities."""
    rels: list[dict[tuple[int, ...], int]] = []
    seen: set = set()

    def visit(n):
        if n in seen:
            return
        seen.add(n)
        if n.is_equals():
            parsed = relation_poly_diff(n.arg(0), n.arg(1), var_index, vars_)
            if parsed is not None:
                diff, modular = parsed
                if modular:
                    quad = {m: c for m, c in diff.items() if len(m) == 2}
                    if quad:
                        rels.append(quad)
        for a in n.args():
            visit(a)

    for cmd in smt_script.commands:
        if cmd.name == "assert":
            visit(cmd.args[0])
    return rels


def _mono(i: int, k: int) -> tuple[int, int]:
    return (i, k) if i <= k else (k, i)


def _pair_reduces(q: dict, i: int, j: int, p: int) -> tuple[bool, bool]:
    """Do ``i`` and ``j`` occur in ``q``'s quadratic part *only* as ``i - j``?

    That holds iff the quadratic coefficients match the ``(i - j)²`` shape not
    just on the diagonal (``coeff(i²)=coeff(j²)``, ``coeff(i·j)=-2·coeff(i²)``)
    but for **every** cross term: ``coeff(i·k) = -coeff(j·k)`` for all other
    ``k``. Only then does substituting ``i → j + d`` cancel ``j`` out of the
    nonlinear part (a diagonal-only match still leaves ``j·k`` terms behind, so
    the rewrite would be sound but useless). Returns ``(matches, has_i2_term)``.
    """
    cii = q.get((i, i), 0) % p
    cjj = q.get((j, j), 0) % p
    if cii != cjj or q.get(_mono(i, j), 0) % p != (-2 * cii) % p:
        return False, False
    ks = {k for m in q for k in m} - {i, j}
    for k in ks:
        if q.get(_mono(i, k), 0) % p != (-q.get(_mono(j, k), 0)) % p:
            return False, False
    return True, cii != 0


def _detect_pairs(rels, p) -> list[tuple[int, int]]:
    """Disjoint ``(i, j)`` index pairs that occur only as ``i - j`` in every relation."""
    squared = {i for q in rels for (a, b) in q if a == b for i in (a,)}
    idxs = sorted(squared)
    chosen: list[tuple[int, int]] = []
    used: set[int] = set()
    for a in range(len(idxs)):
        for b in range(a + 1, len(idxs)):
            i, j = idxs[a], idxs[b]
            if i in used or j in used:
                continue
            all_ok = True
            coupled = False
            for q in rels:
                matches, has_sq = _pair_reduces(q, i, j, p)
                if not matches:
                    all_ok = False
                    break
                coupled = coupled or has_sq
            if all_ok and coupled:
                used.add(i)
                used.add(j)
                chosen.append((i, j))
    return chosen


def simplify_diff_vars(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Replace ``x`` by ``y + d`` for difference pairs ``(x, y)``; a no-op otherwise."""
    vars_ = collect_variables(smt_script)
    var_index = {s: i for i, s in enumerate(vars_)}
    rels = _modular_quadratics(smt_script, var_index, vars_)
    pairs = _detect_pairs(rels, _field_p()) if rels else []
    if not pairs:
        stats_dump("diff_vars", {"pairs": 0})
        return smt_script

    submap: dict = {}
    defs: list[tuple[FNode, FNode, FNode]] = []  # (x, y, d)
    for i, j in pairs:
        x, y = vars_[i], vars_[j]
        d = Symbol(f"{x.symbol_name()}!diff", INT)
        submap[x] = Plus(y, d)
        defs.append((x, y, d))

    for cmd in smt_script.commands:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(cmd.args[0].substitute(submap), cmd.args[0])

    # Declare each ``d`` BEFORE the first assert -- the substituted asserts above
    # reference it, and SMT-LIB requires declaration before use (otherwise the
    # solver errors on the unknown symbol and silently drops those asserts,
    # losing constraints and yielding a spurious ``sat``). ``x`` keeps its own
    # declaration; pin ``x = y + d`` so the change of variables stays
    # equisatisfiable and ``x`` still appears in counterexample models.
    first_assert = next(
        (k for k, c in enumerate(smt_script.commands) if c.name == "assert"),
        len(smt_script.commands),
    )
    decls = [
        script.SmtLibCommand(name="declare-fun", args=[d, d.get_type()])
        for _, _, d in defs
    ]
    smt_script.commands[first_assert:first_assert] = decls
    check_idx = next(
        (k for k, c in enumerate(smt_script.commands) if c.name == "check-sat"),
        len(smt_script.commands),
    )
    pins = [
        script.SmtLibCommand(name="assert", args=[Equals(x, Plus(y, d))])
        for x, y, d in defs
    ]
    smt_script.commands[check_idx:check_idx] = pins

    # This pass runs last (after ``z3-solve-eqs``), so there is no later
    # ``normalize`` to expand the substituted ``(y + d)`` products and cancel
    # ``y`` from the nonlinear part -- do it here. (Running normalize earlier and
    # then z3-solve-eqs would let solve-eqs re-derive ``x - y`` and undo us.)
    smt_script = simplify_normalize(smt_script)

    names = [(x.symbol_name(), y.symbol_name()) for x, y, _ in defs]
    logging.info("diff_vars: substituted %d difference pair(s): %s", len(defs), names)
    stats_dump("diff_vars", {"pairs": len(defs), "pair_vars": names})
    if subaction is not None:
        subaction += {"pairs": len(defs)}
    return smt_script
