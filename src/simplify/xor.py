from typing import Iterable

from ..bus_interactions.openvm_bitwise_lookup import OpenVMBitwiseLookupEncoder
from ..smt.utils import *

UF_XOR = OpenVMBitwiseLookupEncoder.UF_XOR


def _collect_xor_terms(formula: FNode) -> set[FNode]:
    terms = set()
    seen = set()
    stack = [formula]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        if node.is_function_application() and node.function_name() == UF_XOR:
            terms.add(node)
        if not (node.is_forall() or node.is_exists()):
            stack.extend(node.args())
    return terms


def _qxor_axioms(_terms: Iterable[FNode] = ()) -> tuple[FNode, ...]:
    x = Symbol("__qxor_x", INT)
    y = Symbol("__qxor_y", INT)
    return (
        ForAll([x], Equals(Function(UF_XOR, [x, Int(0)]), x)),
        ForAll([x], Equals(Function(UF_XOR, [Int(0), x]), x)),
        ForAll([x], Equals(Function(UF_XOR, [x, x]), Int(0))),
        ForAll(
            [x, y],
            Implies(Equals(Function(UF_XOR, [x, y]), x), Equals(y, Int(0))),
        ),
        ForAll(
            [x, y],
            Implies(Equals(Function(UF_XOR, [y, x]), x), Equals(y, Int(0))),
        ),
    )


def _gxor_axioms(terms: Iterable[FNode]) -> Iterable[FNode]:
    for term in terms:
        x, y = term.args()
        if x == y:
            yield Equals(term, Int(0))
        else:
            yield Iff(Equals(x, Int(0)), Equals(term, y))
            yield Iff(Equals(y, Int(0)), Equals(term, x))
            yield Iff(Equals(x, term), Equals(y, Int(0)))
            yield Iff(Equals(y, term), Equals(x, Int(0)))


class XOrQuantifierSubstituter(substituter.Substituter):
    def __init__(self, axiom_builder, env=None):
        substituter.Substituter.__init__(self, env=env)
        self.axiom_builder = axiom_builder

    @substituter.handles(
        set(operators.ALL_TYPES)
        - frozenset([operators.FORALL, operators.EXISTS, operators.FUNCTION])
    )
    def walk_identity(self, formula, args, **kwargs):
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.FUNCTION]))
    def walk_function(self, formula, args, **kwargs):
        if formula.function_name() == UF_XOR:
            x, y = args
            if x.is_zero():
                return keep_comment(y, formula)
            if y.is_zero():
                return keep_comment(x, formula)
            if x == y:
                return keep_comment(Int(0), formula)
        return keep_comment(Function(formula.function_name(), args), formula)

    @substituter.handles(frozenset([operators.FORALL, operators.EXISTS]))
    def walk_quantifier(self, formula, args, **kwargs):
        qvars = list(formula.quantifier_vars())
        qvarset = frozenset(qvars)
        body = self.substitute(formula.arg(0))
        local_terms = {
            term
            for term in _collect_xor_terms(body)
            if term.get_free_variables() & qvarset
        }
        if local_terms:
            local_axioms = list(without_trues(self.axiom_builder(local_terms)))
            if local_axioms:
                body = And(body, *local_axioms)
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)


def _simplify_xor(smt_script: script.SmtLibScript, axiom_builder) -> script.SmtLibScript:
    injector = XOrQuantifierSubstituter(axiom_builder)
    output = []
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = injector.substitute(cmd.args[0])
            output.append(cmd)
            terms = _collect_xor_terms(cmd.args[0])
            if terms:
                output.extend(
                    script.SmtLibCommand(name="assert", args=[axiom])
                    for axiom in without_trues(axiom_builder(terms))
                )
        else:
            output.append(cmd)
    smt_script.commands = output
    return smt_script


def simplify_qxor(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    return _simplify_xor(smt_script, _qxor_axioms)


def simplify_gxor(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    return _simplify_xor(smt_script, _gxor_axioms)
