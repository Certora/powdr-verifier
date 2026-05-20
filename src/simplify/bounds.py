import re

from ..smt.utils import *

_BOUNDED_INT_VAR_RE = re.compile(r"@[0-9]+$")


def _needs_basic_range_axiom(sym: FNode) -> bool:
    return (
        sym.is_symbol()
        and sym.get_type().is_int_type()
        and _BOUNDED_INT_VAR_RE.search(sym.symbol_name()) is not None
    )


class BoundsQuantifierSubstituter(substituter.Substituter):
    """Walk quantifiers without changing them (injecting range guards inside is unsound)."""

    @substituter.handles(
        set(operators.ALL_TYPES) - frozenset([operators.FORALL, operators.EXISTS])
    )
    def walk_identity(self, formula, args, **kwargs):
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.FORALL, operators.EXISTS]))
    def walk_quantifier(self, formula, args, **kwargs):
        qvars = list(formula.quantifier_vars())
        body = args[0]
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)


def simplify_bounds(smt_script: script.SmtLibScript) -> script.SmtLibScript:
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
    return smt_script
