"""Skolem pin metadata for derived columns (``:skolem-<kind>-*``).

Builds :class:`SetInfos` with pin equations and any UF ``declare-fun``s needed
for round-trip parsing.
"""
import logging

from . import SetInfos, SkolemPin, SkolemPinKind
from ..smt.utils import *


def _vars_only(symbols: frozenset[FNode]) -> frozenset[FNode]:
    """Drop UF function-typed symbols, keep plain variables.

    Used by the ``live`` filter on emitted pins: UFs (``uf_mod_inv``,
    ``pc_a``, etc.) are constant globals known to every encoding even
    when they happen to be unused in the actual constraints, so we
    don't want a derived equation to be filtered out merely because it
    mentions a UF the formula didn't reach. Whatever UFs the pins do
    reference are collected separately by :func:`_pin_ufs` and emitted
    as ``declare-fun``s when emitting the SMT-LIB script.
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
    """Return the equations from a ``derived`` / ``substitutions`` dict.

    Both ``after_smt.derived`` (derived columns) and
    ``before_conv.convert_substitutions(...)`` already canonicalize their
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
    for n in iter_unique_subnodes(formula):
        if n.is_symbol():
            out.add(n)
        if n.is_quantifier():
            for q in n.quantifier_vars():
                if q.is_symbol():
                    out.add(q)
    return frozenset(out)


def drop_mirrored_derived(
    derived: dict[FNode, FNode],
    other_derived: dict[FNode, FNode],
    prefix: str,
    other_prefix: str,
) -> dict[FNode, FNode]:
    """Drop derived columns that the other side defines identically.

    When before and after dumps share a derived column (same name and
    same defining expression modulo the ``before-``/``after-`` prefix),
    do not emit a functional ``:skolem-derived-`` pin for it: the
    ``skolem_names`` same-name fallback then pins the quantified copy to
    its free counterpart, which is an equally valid witness and a far
    better one downstream — identity pins survive every simplifier
    pass, whereas ``simplify_mod_inv``'s definition-level fold rewrites
    functional ``QuotientOrZero`` pins into a pair of relational
    implications, losing witness determinism and forcing the solver
    into modular-inverse uniqueness reasoning.

    Columns without an identical counterpart keep their functional pin
    (the only valid witness when the circuits genuinely differ).
    """
    other_stripped = {
        strip_prefix_from_vars(k, other_prefix): strip_prefix_from_vars(eq, other_prefix)
        for k, eq in other_derived.items()
    }
    out: dict[FNode, FNode] = {}
    for k, eq in derived.items():
        ks = strip_prefix_from_vars(k, prefix)
        if other_stripped.get(ks) == strip_prefix_from_vars(eq, prefix):
            logging.info("derived pin dropped (mirrored on both sides): %s", k)
            continue
        out[k] = eq
    return out


def derived_columns_skolem_setinfo(
    formula: FNode,
    derived: dict[FNode, FNode],
    *,
    kind: SkolemPinKind = SkolemPinKind.DERIVED,
) -> SetInfos:
    """Produce pin equations / decls for skolem pins (``:skolem-<kind>-*``).

    ``kind`` is applied to each :class:`SkolemPin` (equations and matching decls).

    Returns a :class:`SetInfos` whose ``equations`` carry the given map's
    ``Equals`` / ``Iff`` pins for the simplifier-side skolem orchestrator
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
    decls = _pin_ufs(derived_pins)
    return SetInfos(
        equations=[SkolemPin(eq, kind) for eq in derived_pins],
        decls=[SkolemPin(d, kind) for d in decls],
    )
