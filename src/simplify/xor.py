"""XOR term handling: either axioms over ``UF_XOR`` or native bit-vector encoding."""
from typing import Iterable

from ..bus_interactions.openvm_bitwise_lookup import OpenVMBitwiseLookupEncoder
from ..smt.utils import *

UF_XOR = OpenVMBitwiseLookupEncoder.UF_XOR


def _collect_xor_terms(formula: FNode) -> set[FNode]:
    """Collect every ``UF_XOR`` application under ``formula`` (skip quantifier bodies for descent)."""
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
    """Universal algebraic axioms for ``UF_XOR`` (identity, nilpotence, cancellation)."""
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
    """Per-term ``UF_XOR(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_gxor``)."""
    for term in terms:
        x, y = term.args()
        if x == y:
            yield Equals(term, Int(0))
        else:
            # x ^ x == 0
            yield Iff(Equals(x, y), Equals(term, Int(0)))
            # 0 ^ y == y
            yield Iff(Equals(x, Int(0)), Equals(term, y))
            # x ^ 0 == x
            yield Iff(Equals(y, Int(0)), Equals(term, x))
            # (0 <= x <= 255) and (y == 255) -> term == 255 - x
            yield Implies(
                And(LE(Int(0), x), LE(x, Int(255)), Equals(y, Int(255))),
                Equals(term, Minus(Int(255), x)),
            )
            # (0 <= y <= 255) and (x == 255) -> term == 255 - y
            yield Implies(
                And(LE(Int(0), y), LE(y, Int(255)), Equals(x, Int(255))),
                Equals(term, Minus(Int(255), y)),
            )
            # (x == term) -> y == 0
            yield Iff(Equals(x, term), Equals(y, Int(0)))
            # (y == term) -> x == 0
            yield Iff(Equals(y, term), Equals(x, Int(0)))


class XOrQuantifierSubstituter(substituter.Substituter):
    """Simplify ``UF_XOR`` under quantifiers and attach ``axiom_builder`` facts local to each scope."""

    def __init__(self, axiom_builder, env=None):
        """``axiom_builder(terms)`` yields extra conjuncts for XOR terms mentioning bound variables."""
        substituter.Substituter.__init__(self, env=env)
        self.axiom_builder = axiom_builder

    @substituter.handles(
        set(operators.ALL_TYPES)
        - frozenset([operators.FORALL, operators.EXISTS, operators.FUNCTION])
    )
    def walk_identity(self, formula, args, **kwargs):
        """Default recursion for non-function, non-quantifier nodes."""
        return keep_comment(
            substituter.Substituter.super(self, formula, args=args, **kwargs), formula
        )

    @substituter.handles(frozenset([operators.FUNCTION]))
    def walk_function(self, formula, args, **kwargs):
        """Constant-fold ``UF_XOR`` at zero / equal arguments."""
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
        """Conjoin quantifier-local XOR axioms for terms that mention bound variables."""
        qvars = list(formula.quantifier_vars())
        qvarset = frozenset(qvars)
        body = args[0]
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


def _simplify_xor(smt_script: script.SmtLibScript, axiom_builder, subaction=None) -> script.SmtLibScript:
    """Shared implementation for ``simplify_qxor`` / ``simplify_gxor``."""
    injector = XOrQuantifierSubstituter(axiom_builder)
    output = []
    top_axiom_asserts = 0
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = injector.substitute(cmd.args[0])
            output.append(cmd)
            terms = _collect_xor_terms(cmd.args[0])
            if terms:
                axioms = list(without_trues(axiom_builder(terms)))
                top_axiom_asserts += len(axioms)
                output.extend(
                    script.SmtLibCommand(name="assert", args=[axiom])
                    for axiom in axioms
                )
        else:
            output.append(cmd)
    smt_script.commands = output
    if subaction is not None:
        subaction += {
            "top_level_xor_axiom_asserts": top_axiom_asserts,
        }
    return smt_script


def simplify_qxor(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Inject global and local ``_qxor_axioms`` for ``UF_XOR``."""
    return _simplify_xor(smt_script, _qxor_axioms, subaction)


def simplify_gxor(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Inject ``_gxor_axioms`` for each distinct ``UF_XOR`` term."""
    return _simplify_xor(smt_script, _gxor_axioms, subaction)
