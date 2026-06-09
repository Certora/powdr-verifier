"""Bitwise UF handling: axioms over ``UF_XOR``, ``UF_AND``, ``UF_OR`` (quantified or grounded lemmas)."""
from typing import Callable, Iterable, NamedTuple

from ..bus_interactions.openvm_bitwise_lookup import OpenVMBitwiseLookupEncoder
from ..smt.utils import *

UF_XOR = OpenVMBitwiseLookupEncoder.UF_XOR
UF_AND = OpenVMBitwiseLookupEncoder.UF_AND
UF_OR = OpenVMBitwiseLookupEncoder.UF_OR


class BitwiseTerms(NamedTuple):
    """Distinct UF application nodes under a formula, split by symbol."""

    xors: frozenset[FNode]
    ands: frozenset[FNode]
    ors: frozenset[FNode]

    def non_empty(self) -> bool:
        return bool(self.xors or self.ands or self.ors)


def _bitwise_stats_template() -> dict:
    """Counters for UF applications ``seen`` and axioms ``emitted`` (``link`` = OR–AND identity)."""
    return {
        "seen": {"xor": 0, "and": 0, "or": 0},
        "emitted": {"xor": 0, "and": 0, "or": 0, "link": 0},
    }


def _note_seen(stats: dict | None, terms: BitwiseTerms) -> None:
    if stats is None:
        return
    s = stats["seen"]
    s["xor"] += len(terms.xors)
    s["and"] += len(terms.ands)
    s["or"] += len(terms.ors)


def _note_emitted(stats: dict | None, kind: str) -> None:
    if stats is None:
        return
    stats["emitted"][kind] += 1


def _counting_axiom_builder(
    tagged: Callable[[BitwiseTerms], Iterable[tuple[str, FNode]]],
    stats: dict | None,
) -> Callable[[BitwiseTerms], Iterable[FNode]]:
    def builder(t: BitwiseTerms) -> Iterable[FNode]:
        for kind, axiom in tagged(t):
            _note_emitted(stats, kind)
            yield axiom

    return builder


def _collect_bitwise_terms(formula: FNode) -> BitwiseTerms:
    """Collect every ``UF_XOR`` / ``UF_AND`` / ``UF_OR`` application under ``formula``.

    Skips quantifier bodies for descent (same scoping rule as the legacy XOR collector).
    """
    xor_t: set[FNode] = set()
    and_t: set[FNode] = set()
    or_t: set[FNode] = set()
    seen: set[FNode] = set()
    stack = [formula]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        if node.is_function_application():
            fn = node.function_name()
            if fn == UF_XOR:
                xor_t.add(node)
            elif fn == UF_AND:
                and_t.add(node)
            elif fn == UF_OR:
                or_t.add(node)
        if not (node.is_forall() or node.is_exists()):
            stack.extend(node.args())
    return BitwiseTerms(
        frozenset(xor_t),
        frozenset(and_t),
        frozenset(or_t),
    )


def _quantified_xor_axioms(_terms: Iterable[FNode] = ()) -> tuple[FNode, ...]:
    """Universal algebraic axioms for ``UF_XOR`` (identity, nilpotence, cancellation)."""
    x = Symbol("__bwx", INT)
    y = Symbol("__bwy", INT)
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


def _quantified_andor_axioms() -> tuple[FNode, ...]:
    """Universal identity linking ``UF_OR`` and ``UF_AND`` (bitwise ``x|y = x+y-(x&y)``)."""
    x = Symbol("__bw_andor_x", INT)
    y = Symbol("__bw_andor_y", INT)
    return (
        ForAll(
            [x, y],
            Equals(
                Function(UF_OR, [x, y]),
                Minus(Plus(x, y), Function(UF_AND, [x, y])),
            ),
        ),
    )


def _qbitwise_axioms_tagged(t: BitwiseTerms) -> Iterable[tuple[str, FNode]]:
    """Quantified XOR algebra plus, when AND/OR appear, the global OR–AND identity."""
    if t.xors:
        for ax in _quantified_xor_axioms():
            yield ("xor", ax)
    if t.ands or t.ors:
        for ax in _quantified_andor_axioms():
            yield ("link", ax)


def _ground_xor_lemmas(terms: Iterable[FNode]) -> Iterable[FNode]:
    """Per-term ``UF_XOR(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_gbitwise``)."""
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


def _ground_and_lemmas(terms: Iterable[FNode]) -> Iterable[FNode]:
    """Per-term ``UF_AND(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_gbitwise``)."""
    for term in terms:
        x, y = term.args()
        if x == y:
            yield Equals(term, x)
        else:
            # x & x == x
            yield Iff(Equals(x, y), Equals(term, x))
            # 0 & y == 0
            yield Iff(Equals(x, Int(0)), Equals(term, Int(0)))
            # x & 0 == 0
            yield Iff(Equals(y, Int(0)), Equals(term, Int(0)))
            # (0 <= x <= 255) and (y == 255) -> term == x  (full byte mask)
            yield Implies(
                And(LE(Int(0), x), LE(x, Int(255)), Equals(y, Int(255))),
                Equals(term, x),
            )
            # (0 <= y <= 255) and (x == 255) -> term == y
            yield Implies(
                And(LE(Int(0), y), LE(y, Int(255)), Equals(x, Int(255))),
                Equals(term, y),
            )


def _ground_or_lemmas(terms: Iterable[FNode]) -> Iterable[FNode]:
    """Per-term ``UF_OR(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_gbitwise``)."""
    for term in terms:
        x, y = term.args()
        if x == y:
            yield Equals(term, x)
        else:
            # x | x == x
            yield Iff(Equals(x, y), Equals(term, x))
            # 0 | y == y
            yield Iff(Equals(x, Int(0)), Equals(term, y))
            # x | 0 == x
            yield Iff(Equals(y, Int(0)), Equals(term, x))
            # (0 <= x <= 255) and (y == 255) -> term == 255
            yield Implies(
                And(LE(Int(0), x), LE(x, Int(255)), Equals(y, Int(255))),
                Equals(term, Int(255)),
            )
            # (0 <= y <= 255) and (x == 255) -> term == 255
            yield Implies(
                And(LE(Int(0), y), LE(y, Int(255)), Equals(x, Int(255))),
                Equals(term, Int(255)),
            )


def _ground_andor_connection_pairs(t: BitwiseTerms) -> Iterable[FNode]:
    """Grounded identity ``or(x,y) = x + y - and(x,y)`` for each argument pair seen on AND/OR."""
    pairs: set[tuple[FNode, FNode]] = set()
    for term in t.ands:
        pairs.add((term.args()[0], term.args()[1]))
    for term in t.ors:
        pairs.add((term.args()[0], term.args()[1]))
    for x, y in pairs:
        # Relates ``uf_or`` and ``uf_and`` for this (x, y) pair (bitwise ``|`` / ``&`` on bytes).
        yield Equals(
            Function(UF_OR, [x, y]),
            Minus(Plus(x, y), Function(UF_AND, [x, y])),
        )


def _gbitwise_axioms_tagged(t: BitwiseTerms) -> Iterable[tuple[str, FNode]]:
    """Merge XOR / AND / OR grounded lemmas plus pairwise OR–AND links."""
    for ax in _ground_xor_lemmas(t.xors):
        yield ("xor", ax)
    for ax in _ground_and_lemmas(t.ands):
        yield ("and", ax)
    for ax in _ground_or_lemmas(t.ors):
        yield ("or", ax)
    for ax in _ground_andor_connection_pairs(t):
        yield ("link", ax)


class BitwiseQuantifierSubstituter(substituter.Substituter):
    """Simplify bitwise UFs under quantifiers and attach ``axiom_builder`` facts local to each scope."""

    def __init__(self, axiom_builder, env=None, stats=None):
        """``axiom_builder(terms)`` yields extra conjuncts for UF terms mentioning bound variables."""
        substituter.Substituter.__init__(self, env=env)
        self.axiom_builder = axiom_builder
        self.stats = stats

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
        """Constant-fold bitwise UFs at zero / equal arguments."""
        fn = formula.function_name()
        if fn == UF_XOR:
            x, y = args
            if x.is_zero():
                return keep_comment(y, formula)
            if y.is_zero():
                return keep_comment(x, formula)
            if x == y:
                return keep_comment(Int(0), formula)
        elif fn == UF_AND:
            x, y = args
            if x.is_zero() or y.is_zero():
                return keep_comment(Int(0), formula)
            if x == y:
                return keep_comment(x, formula)
        elif fn == UF_OR:
            x, y = args
            if x.is_zero():
                return keep_comment(y, formula)
            if y.is_zero():
                return keep_comment(x, formula)
            if x == y:
                return keep_comment(x, formula)
        return keep_comment(Function(formula.function_name(), args), formula)

    @substituter.handles(frozenset([operators.FORALL, operators.EXISTS]))
    def walk_quantifier(self, formula, args, **kwargs):
        """Conjoin quantifier-local axioms for bitwise UF terms that mention bound variables."""
        qvars = list(formula.quantifier_vars())
        qvarset = frozenset(qvars)
        body = args[0]
        full = _collect_bitwise_terms(body)
        local = BitwiseTerms(
            frozenset(t for t in full.xors if t.get_free_variables() & qvarset),
            frozenset(t for t in full.ands if t.get_free_variables() & qvarset),
            frozenset(t for t in full.ors if t.get_free_variables() & qvarset),
        )
        if local.non_empty():
            _note_seen(self.stats, local)
            local_axioms = list(without_trues(self.axiom_builder(local)))
            if local_axioms:
                body = And(body, *local_axioms)
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)


def _simplify_bitwise(
    smt_script: script.SmtLibScript,
    tagged_axioms: Callable[[BitwiseTerms], Iterable[tuple[str, FNode]]],
    subaction=None,
) -> script.SmtLibScript:
    """Shared implementation for ``simplify_qbitwise`` / ``simplify_gbitwise``."""
    stats = _bitwise_stats_template() if subaction is not None else None
    counting_builder = _counting_axiom_builder(tagged_axioms, stats)
    injector = BitwiseQuantifierSubstituter(counting_builder, stats=stats)
    output = []
    top_axiom_asserts = 0
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = injector.substitute(cmd.args[0])
            output.append(cmd)
            terms = _collect_bitwise_terms(cmd.args[0])
            if terms.non_empty():
                _note_seen(stats, terms)
                axioms = list(without_trues(counting_builder(terms)))
                top_axiom_asserts += len(axioms)
                output.extend(
                    script.SmtLibCommand(name="assert", args=[axiom])
                    for axiom in axioms
                )
        else:
            output.append(cmd)
    smt_script.commands = output
    if subaction is not None:
        # Counts every extra assert from this pass (XOR, AND, OR, and connection lemmas).
        payload: dict = {"top_level_bitwise_axiom_asserts": top_axiom_asserts}
        if stats is not None:
            payload["bitwise_stats"] = stats
        subaction += payload
    return smt_script


def simplify_qbitwise(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Inject global and local quantified axioms for bitwise UFs."""
    return _simplify_bitwise(smt_script, _qbitwise_axioms_tagged, subaction)


def simplify_gbitwise(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Inject grounded lemmas for each distinct bitwise UF application."""
    return _simplify_bitwise(smt_script, _gbitwise_axioms_tagged, subaction)
