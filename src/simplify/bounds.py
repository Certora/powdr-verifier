"""Inject field-range axioms for bounded integer symbols (suffix ``@…`` pattern)."""
import re

from ..smt.utils import *
from ..utils.stats import stats_dump

_BOUNDED_INT_VAR_RE = re.compile(r"@[0-9]+$")


def _needs_basic_range_axiom(sym: FNode) -> bool:
    """True for int symbols whose names end with ``@<digits>`` (bounded APC columns)."""
    return (
        sym.is_symbol()
        and sym.get_type().is_int_type()
        and _BOUNDED_INT_VAR_RE.search(sym.symbol_name()) is not None
    )


class BoundsQuantifierSubstituter(substituter.Substituter):
    """Walk quantifiers without changing them (injecting range guards inside is unsound)."""

    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    @substituter.handles(
        set(operators.ALL_TYPES) - frozenset([operators.FORALL, operators.EXISTS])
    )
    def walk_identity(self, formula, args, **kwargs):
        """Recurse under non-quantifier nodes unchanged."""
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.FORALL, operators.EXISTS]))
    def walk_quantifier(self, formula, args, **kwargs):
        """Leave quantifier structure unchanged (bounds are injected as separate asserts)."""
        qvars = list(formula.quantifier_vars())
        body = args[0]
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)


def simplify_bounds(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """After a preserving walk, prepend ``field_symbol`` asserts for bounded ``@…`` int columns."""
    injector = BoundsQuantifierSubstituter(env=get_env())
    bounded_symbols = set()
    rewritten = []

    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = injector.substitute(cmd.args[0])
            bounded_symbols.update(
                sym
                for sym in cmd.args[0].get_free_variables()
                if _needs_basic_range_axiom(sym)
            )
        rewritten.append(cmd)

    if not bounded_symbols:
        stats_dump("bounds", {"bounded_symbols": 0, "range_asserts_added": 0})
        return smt_script

    bound_asserts = [
        script.SmtLibCommand(name="assert", args=[field_symbol(sym)])
        for sym in sorted(bounded_symbols, key=str)
    ]

    output = []
    inserted = False
    for cmd in rewritten:
        if not inserted and cmd.name == "assert":
            output.extend(bound_asserts)
            inserted = True
        output.append(cmd)

    smt_script.commands = output
    stats_dump(
        "bounds",
        {
            "bounded_symbols": len(bounded_symbols),
            "range_asserts_added": len(bound_asserts),
        },
    )
    return smt_script
