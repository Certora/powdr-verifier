"""Bitwise UF handling: grounded lemmas over ``UF_XOR``, ``UF_AND``, ``UF_OR``."""
from typing import Iterable, Iterator, NamedTuple

from ..bus_interactions.openvm_bitwise_lookup import OpenVMBitwiseLookupEncoder
from ..smt.utils import *
from ..utils.stats import stats_dump, stats_enabled

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


def _bitwise_terms_for_scope(
    formula: FNode, qvarset: frozenset[FNode] | None
) -> BitwiseTerms:
    """Collect ``UF_*`` apps under ``formula`` (not descending into quantifier bodies).

    If ``qvarset`` is set, keep only applications whose free variables intersect it.
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
                if qvarset is None or node.get_free_variables() & qvarset:
                    xor_t.add(node)
            elif fn == UF_AND:
                if qvarset is None or node.get_free_variables() & qvarset:
                    and_t.add(node)
            elif fn == UF_OR:
                if qvarset is None or node.get_free_variables() & qvarset:
                    or_t.add(node)
        if not (node.is_forall() or node.is_exists()):
            stack.extend(node.args())
    return BitwiseTerms(
        frozenset(xor_t),
        frozenset(and_t),
        frozenset(or_t),
    )


def _ground_linking_lemmas(t: BitwiseTerms) -> Iterable[FNode]:
    """Per-``UF_XOR(x,y)`` linking lemmas tying XOR to AND/OR, byte-guarded.

    This is the *symmetric* fix for the AND/OR byte-range asymmetry: keyed off
    the ``uf_xor`` application itself, it is emitted for every ``uf_xor`` term
    on *both* sides of a VC, regardless of whether the per-row recognizer
    (`openvm_bitwise_lookup._and_or_target`) fired. The recognizer fires only
    on *folded* rows (post ``solver`` pass), so on the multiplexed pre-solver
    side the result column is otherwise left without a byte range -> the side
    that DID recognize is strictly stronger -> spurious ``sat`` (guest-keccak
    2105476 002->003). Making this an axiom removes the dependence on
    recognition entirely.

    The linking block ``x + y = uf_xor(x,y) + 2·uf_and(x,y)`` (the lost evenness of
    ``2·AND``) combined with the row's table fact ``uf_xor(x,y) = z`` forces
    ``a = uf_and(x,y)`` for an AND row (``z = x+y-2a``) — exactly what the
    recognizer asserts, but now on both sides. ``uf_or`` is tied via
    ``x|y = x+y - x&y`` (its byte range is not a linear consequence, so it is
    asserted explicitly). Guarded by ``byte(x) and byte(y)`` (the relations
    only hold for bytes); the guard is discharged from the per-row range
    asserts the bitwise encoder already emits.
    """
    for term in t.xors:
        x, y = term.args()
        if x == y:
            continue
        conj = Function(UF_AND, [x, y])
        disj = Function(UF_OR, [x, y])
        guard = And(LE(Int(0), x), LE(x, Int(255)), LE(Int(0), y), LE(y, Int(255)))
        # x + y = (x ^ y) + 2·(x & y)
        yield Implies(guard, Equals(Plus(x, y), Plus(term, Times(Int(2), conj))))
        # x & y is a byte bounded by both operands
        yield Implies(guard, And(LE(Int(0), conj), LE(conj, x), LE(conj, y)))
        # x | y = x + y - (x & y), and is a byte (NOT a linear consequence)
        yield Implies(
            guard,
            And(Equals(disj, Minus(Plus(x, y), conj)), LE(Int(0), disj), LE(disj, Int(255))),
        )


def _ground_xor_lemmas(t: BitwiseTerms) -> Iterable[FNode]:
    """Per-term ``UF_XOR(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_bitwise``)."""
    for term in t.xors:
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


def _ground_and_lemmas(t: BitwiseTerms) -> Iterable[FNode]:
    """Per-term ``UF_AND(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_bitwise``)."""
    for term in t.ands:
        x, y = term.args()
        if x == y:
            yield Equals(term, x)
        else:
            # x == y  ->  x & y == x
            yield Implies(Equals(x, y), Equals(term, x))
            # x == 0  ->  x & y == 0
            yield Implies(Equals(x, Int(0)), Equals(term, Int(0)))
            # y == 0  ->  x & y == 0
            yield Implies(Equals(y, Int(0)), Equals(term, Int(0)))
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


def _ground_or_lemmas(t: BitwiseTerms) -> Iterable[FNode]:
    """Per-term ``UF_OR(x,y)`` lemmas for 8-bit-style bounds (used with ``simplify_bitwise``)."""
    for term in t.ors:
        x, y = term.args()
        if x == y:
            yield Equals(term, x)
        else:
            # x == y  ->  x | y == x
            yield Implies(Equals(x, y), Equals(term, x))
            # x == 0  ->  x | y == y
            yield Implies(Equals(x, Int(0)), Equals(term, y))
            # y == 0  ->  x | y == x
            yield Implies(Equals(y, Int(0)), Equals(term, x))
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


def _conjoin_axioms_flat(body: FNode, axioms: Iterable[FNode]) -> FNode:
    axs = list(axioms)
    if not axs:
        return body
    parts = list(body.args()) if body.is_and() else [body]
    parts.extend(axs)
    return And(*parts)


class BitwiseQuantifierSubstituter(substituter.Substituter):
    """Simplify bitwise UFs under quantifiers and attach bitwise axiom conjuncts.

    Expects ``env.bitwise_axiom_generators`` (sequence of
    ``(BitwiseTerms) -> Iterable[(str, FNode)]``) and optionally
    ``env.bitwise_stats`` while ``substitute`` / ``bitwise_lemmas`` run.
    """

    def __init__(self, env=None):
        substituter.Substituter.__init__(self, env=env)

    def bitwise_lemmas(
        self,
        body: FNode,
        qvarset: frozenset[FNode] | None,
        dedupe: set[FNode],
    ) -> Iterator[FNode]:
        t = _bitwise_terms_for_scope(body, qvarset)
        if not t.non_empty():
            return
        stats = getattr(self.env, "bitwise_stats", None)
        if stats is not None:
            _note_seen(stats, t)
        gens = getattr(self.env, "bitwise_axiom_generators", ())
        for gen in gens:
            for kind, axiom in gen(t):
                if axiom is None or axiom.is_true():
                    continue
                if axiom in dedupe:
                    continue
                dedupe.add(axiom)
                _note_emitted(stats, kind)
                yield axiom

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
        body = _conjoin_axioms_flat(
            body, self.bitwise_lemmas(body, qvarset, set())
        )
        if formula.is_forall():
            return keep_comment(ForAll(qvars, body), formula)
        return keep_comment(Exists(qvars, body), formula)


def simplify_bitwise(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Inject grounded lemmas for each distinct bitwise UF application.

    Runs the pipeline twice on the full script: first linking lemmas only, then
    XOR / AND / OR lemmas (after link axioms are present in formulas and as
    asserts). Top-level additions are de-duplicated by formula node identity
    across both passes.
    """
    stats = None
    if stats_enabled():
        stats = {
            "seen": {"xor": 0, "and": 0, "or": 0},
            "emitted": {"xor": 0, "and": 0, "or": 0, "link": 0},
        }
    env = get_env()
    if stats is not None:
        env.bitwise_stats = stats
    seen_top_axioms: set[FNode] = set()
    top_axiom_asserts = 0
    try:
        for generators in (
            (lambda t: (("link", ax) for ax in _ground_linking_lemmas(t)),),
            (
                lambda t: (("xor", ax) for ax in _ground_xor_lemmas(t)),
                lambda t: (("and", ax) for ax in _ground_and_lemmas(t)),
                lambda t: (("or", ax) for ax in _ground_or_lemmas(t)),
            ),
        ):
            env.bitwise_axiom_generators = generators
            subst = BitwiseQuantifierSubstituter(env)
            output = []
            for cmd in smt_script:
                if cmd.name == "assert":
                    cmd.args[0] = subst.substitute(cmd.args[0])
                    output.append(cmd)
                    for axiom in subst.bitwise_lemmas(cmd.args[0], None, seen_top_axioms):
                        top_axiom_asserts += 1
                        output.append(script.SmtLibCommand(name="assert", args=[axiom]))
                else:
                    output.append(cmd)
            smt_script.commands = output
    finally:
        for name in ("bitwise_axiom_generators", "bitwise_stats"):
            if hasattr(env, name):
                delattr(env, name)
    payload: dict = {"top_level_bitwise_axiom_asserts": top_axiom_asserts}
    if stats is not None:
        payload["bitwise_stats"] = stats
    stats_dump("bitwise", payload)
    return smt_script
