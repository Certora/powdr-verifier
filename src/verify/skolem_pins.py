"""Set-info for derived-column skolem pins (``:skolem-derived-*``).

Builds ``SetInfo`` fragments that pair quantified variables with witness
expressions from derived column definitions and declares any UF symbols
those pins reference.
"""
from . import SetInfo
from ..simplify.skolem_derived import SETINFO_PREFIX as SETINFO_DERIVED_PREFIX
from ..simplify.skolem_utils import emit_pin_setinfo
from ..smt.utils import *


def _eq_pin_setinfo(prefix: str, pins: list[FNode]) -> list:
    """Wrap each pin equation as a ``set-info :{prefix}N`` command.

    Pins are kept as ``Equals(var, expr)`` ``FNode`` instances; the
    simplifier-side parser splits them into qvar and witness.
    """
    return [emit_pin_setinfo(prefix, i, eq) for i, eq in enumerate(pins)]


def _vars_only(symbols: frozenset[FNode]) -> frozenset[FNode]:
    """Drop UF function-typed symbols, keep plain variables.

    Used by the ``live`` filter on emitted pins: UFs (``uf_mod_inv``,
    ``pc_a``, etc.) are constant globals known to every encoding even
    when they happen to be unused in the actual constraints, so we
    don't want a derived equation to be filtered out merely because it
    mentions a UF the formula didn't reach. Whatever UFs the pins do
    reference are collected separately by :func:`_pin_ufs` and emitted
    as ``declare-fun``s alongside the set-info commands.
    """
    return frozenset(
        s for s in symbols if not s.symbol_type().is_function_type()
    )


def _pin_ufs(pins: list[FNode]) -> list[FNode]:
    """Return the UF function symbols referenced by ``pins``."""
    ufs: set[FNode] = set()
    for eq in pins:
        for s in eq.get_free_variables():
            if s.symbol_type().is_function_type():
                ufs.add(s)
    return sorted(ufs, key=lambda s: s.symbol_name())


def _derived_pins(
    derived: dict[FNode, FNode],
    live: frozenset[FNode],
) -> list[FNode]:
    """Return the equations from a ``derived`` / ``eliminations`` dict.

    Both ``after_smt.derived`` (derived columns) and
    ``before_conv.convert_eliminations(...)`` already canonicalize their
    values as ``Equals(var, expr)``. We only emit equations all of whose
    *variable* free symbols appear in ``live``: anything else references
    a variable the encoder has already eliminated and whose
    ``declare-fun`` will not be in the SMT script the simplifier reads
    back, so the round-trip parse would fail. UF function symbols are
    excluded from this check (see :func:`_vars_only`).
    """
    var_live = _vars_only(live)
    out: list[FNode] = []
    for eq in derived.values():
        if _vars_only(eq.get_free_variables()) > var_live:
            continue
        out.append(eq)
    return out


def _collect_all_symbols(formula: FNode) -> frozenset[FNode]:
    """Return every symbol that occurs in ``formula`` (free or bound).

    ``FNode.get_free_variables`` excludes quantifier-bound vars; pins
    may reference vars that only appear as forall qvars, so we walk
    explicitly.
    """
    out: set[FNode] = set()

    def visit(n: FNode):
        if n.is_symbol():
            out.add(n)
        if n.is_quantifier():
            for q in n.quantifier_vars():
                if q.is_symbol():
                    out.add(q)
        for a in n.args():
            visit(a)

    visit(formula)
    return frozenset(out)


def derived_columns_skolem_setinfo(
    formula: FNode,
    derived: dict[FNode, FNode],
) -> SetInfo:
    """Produce set-info / decls for derived-column skolem pins (``:skolem-derived-*``).

    Returns a :class:`SetInfo` whose ``cmds`` carry ``derived`` column
    (and, in soundness, merged ``elimination``) equations for the
    simplifier-side skolem orchestrator
    (:mod:`.simplify.skolem`);
    ``decls`` lists the UF function symbols referenced by those pins so
    :func:`convert_to_smt_script` can emit ``declare-fun``s for them
    even when no constraint of the formula happens to reach them (e.g.
    ``uf_mod_inv`` for derived columns of the form
    ``v = ite(d=0, 0, 1*uf_mod_inv(d))``).

    Pin equations whose *variable* free symbols are not free in
    ``formula`` are still filtered out: those variables will not be
    declared in the smt2 file and the parser would fail to resolve
    them back.
    """
    live = _collect_all_symbols(formula)
    derived_pins = _derived_pins(derived, live)
    cmds = _eq_pin_setinfo(SETINFO_DERIVED_PREFIX[1:], derived_pins)
    return SetInfo(cmds, _pin_ufs(derived_pins))
