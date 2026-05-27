"""SMT-LIB script driver wiring ``IntervalReasoner`` into simplify tactics."""
from __future__ import annotations

import logging

from ...smt.utils import *
from .bounded_formula import BoundedFormula
from .domain import IntVarDomains
from .reasoner import IntervalReasoner, logger as interval_logger


def _has_bottom_domain(reasoner: IntervalReasoner) -> bool:
    """True if any variable's abstract domain became empty after propagation."""
    return any(dom.is_bottom() for dom in reasoner.env.values())


def _is_simple_atomic_bound(f: FNode) -> bool:
    """True for ``<|<=|=`` between one int constant and one int symbol."""
    if not (f.is_le() or f.is_lt() or f.is_equals()):
        return False
    a, b = f.args()
    return (a.is_int_constant() and b.is_symbol()) or (b.is_int_constant() and a.is_symbol())


def simplify_intervals(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Run disjunctive interval propagation on all assertions."""
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    if not assertions:
        if subaction is not None:
            subaction += {"asserts": 0, "inconsistent": False, "tightened_symbols": 0}
        return smt_script

    if interval_logger.isEnabledFor(logging.INFO):
        interval_logger.info("intervals: simplify_intervals processing %d assertions", len(assertions))

    reasoner = IntervalReasoner()
    reasoner.assume_all(assertions, context="simplify_intervals")
    inconsistent = _has_bottom_domain(reasoner)

    if interval_logger.isEnabledFor(logging.INFO):
        interval_logger.info(
            "intervals: propagation done (inconsistent=%s, tightened_symbols=%d)",
            inconsistent,
            len(reasoner.tightened_symbols),
        )

    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        original = cmd.args[0]
        retain = reasoner.must_retain_formula(original)
        if inconsistent:
            cmd.args[0] = Bool(False)
        elif retain:
            # Keep source-level strengthening constraints explicit, but still
            # run quantifier-bound injection and local rewrites.
            cmd.args[0] = reasoner.simplify(
                cmd.args[0],
                prune=False,
                inject_quantifier_bounds=True,
            )
        else:
            cmd.args[0] = reasoner.simplify(
                cmd.args[0],
                prune=True,
                inject_quantifier_bounds=True,
            )
        if (
            not inconsistent
            and not original.is_forall()
            and not original.is_exists()
            and (not retain or not _is_simple_atomic_bound(original))
        ):
            cmd.args[0] = reasoner.inject_root_bounds(cmd.args[0], only_tightened=True)

    if subaction is not None:
        subaction += {
            "asserts": len(assertions),
            "inconsistent": inconsistent,
            "tightened_symbols": len(reasoner.tightened_symbols),
        }
    return smt_script


def simplify_intervals2(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Interval-style propagation using ``BoundedFormula.refine_recursive`` (alternative to ``simplify_intervals``).

    All assertions are conjoined, refined on a single ``BoundedFormula`` tree, then the
    rebuilt formula is written to the first ``assert``; remaining ``assert`` commands are
    set to ``true`` (semantically the conjunction of all asserts is unchanged). If the
    abstract domain becomes bottom, every assert is replaced with ``false``.
    """

    prefix = []
    assertions = []
    suffix = []

    in_suffix = False
    for cmd in smt_script:
        if in_suffix:
            suffix.append(cmd)
            continue
        match cmd.name:
            case "set-info" | "set-logic" | "set-option" | "get-model" | "get-unsat-core" | "echo" | "declare-fun":
                prefix.append(cmd)
            case "assert":
                assertions.append(cmd.args[0])
            case "check-sat":
                in_suffix = True
                suffix.append(cmd)
            case _:
                assert False, f"unexpected command: {cmd.name}"
    
    n_asserts_in = len(assertions)
    if not assertions:
        if subaction is not None:
            subaction += {"asserts_in": 0, "asserts_out": 0, "inconsistent": False}
        return smt_script

    if interval_logger.isEnabledFor(logging.INFO):
        interval_logger.info("intervals: simplify_intervals2 processing %d assertions", len(assertions))

    combined = And(*assertions) if len(assertions) > 1 else assertions[0]
    bf = BoundedFormula(combined)
    bf.refine_recursive()
    inconsistent = bf.domains.is_bottom()

    if interval_logger.isEnabledFor(logging.INFO):
        interval_logger.info(
            "intervals: simplify_intervals2 propagation done (inconsistent=%s)",
            inconsistent,
        )

    if inconsistent:
        assertions = FALSE()
    else:
        bf.simplify(IntVarDomains.top(), frozenset())
        res = bf.as_fnode()
        assert res.is_and()
        assertions = [
            script.SmtLibCommand(name="assert", args=[a]) for a in res.args()
        ]

    res = script.SmtLibScript()
    res.commands = prefix + assertions + suffix
    if subaction is not None:
        out_asserts = sum(1 for c in res.commands if c.name == "assert")
        subaction += {
            "asserts_in": n_asserts_in,
            "asserts_out": out_asserts,
            "inconsistent": inconsistent,
        }
    return res
