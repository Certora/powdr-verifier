"""Shared PySMT helpers: comments, models, field axioms, and SMT-LIB I/O."""
import enum
import functools
import itertools
import logging
from pathlib import Path
from typing import Any, Iterable, NamedTuple
from types import GeneratorType

from ..smt_backends.pysmt import *
from ..utils.io import open_file
# Imported after the backend's ``import *`` so its custom-operator and
# type-checker setup runs first (importing this earlier breaks ``MOD``).
from pysmt.environment import get_env
from pysmt.walkers import IdentityDagWalker

SUPPORTS_COMMENTS = "comment" in FNode.__slots__

_identity_walker: IdentityDagWalker | None = None


def _refresh_formula(f: FNode) -> FNode:
    """Rebuild ``f`` with fresh nodes so ``simplify()`` can apply further rules.

    Equivalent to ``substitute({}, {})`` but skips MGSubstituter's empty-map overhead.
    """
    global _identity_walker
    if _identity_walker is None:
        _identity_walker = IdentityDagWalker(get_env())
    return _identity_walker.walk(f)


_BOOL_CONNECTIVES = frozenset(
    {operators.AND, operators.OR, operators.NOT, operators.IMPLIES, operators.IFF}
)


def bool_simplify(formula: FNode, memo: dict[FNode, FNode] | None = None) -> FNode:
    """Simplify only the boolean skeleton, leaving theory atoms untouched.

    Recurses through boolean connectives (And/Or/Not/Implies/Iff) applying pysmt's
    own per-node simplify rules, but **stops at every non-connective node** (theory
    atoms like ``field_eq``/mod-equalities, symbols, constants) and returns it as-is
    -- it never descends into or rebuilds arithmetic. So this does NOT do deep
    (theory) simplification, only boolean. Sound (boolean simplifications are
    logically equivalent and atoms are returned unchanged); cheap (O(boolean
    skeleton), not O(whole formula)). Used as a presimplifier when only boolean
    unit structure matters and theory atoms are either already simplified or
    irrelevant.

    Pass a shared ``memo`` when simplifying many formulas that reuse subexpressions
    (e.g. plain permutation conjunct batches).
    """
    simp = get_env().simplifier
    fns = simp.functions
    local_memo = memo if memo is not None else {}

    def go(f: FNode) -> FNode:
        cached = local_memo.get(f)
        if cached is not None:
            return cached
        if f.node_type() in _BOOL_CONNECTIVES:
            r = fns[f.node_type()](f, [go(a) for a in f.args()])
        else:
            r = f
        local_memo[f] = r
        return r

    return go(formula)


def bool_substitute_simplify(formula: FNode, subs: dict) -> FNode:
    """Fused substitution + simplification in one pruned, bottom-up pass.

    Replaces ``substitute(formula, subs).simplify()`` -- two full DAG walks -- with a
    single pruned walk. ``substitute_no_validate``/``FNode.substitute`` rebuild the
    *entire* tree regardless of where the keys occur, so replacing a boolean symbol
    in a formula whose mass is large arithmetic atoms re-walks all that arithmetic
    for nothing (measured ~57x overhead). Here:

    * **Prune** -- a node whose (memoized) free vars are disjoint from the keys is
      returned unchanged without recursing. When the keys are boolean symbols that
      occur only in the boolean skeleton, recursion stops at every theory atom.
    * **Fuse** -- as the boolean skeleton is rebuilt, each node is simplified in the
      same pass by dispatching into the environment ``Simplifier``'s own per-node
      ``walk_*`` rule (``simp.functions[node_type]``), so the boolean simplification
      is *identical* to ``.simplify()`` (set-dedup, complement detection, constant
      folding -- not just TRUE/FALSE folding).

    Sound and equivalent to ``substitute(formula, subs).simplify()`` provided
    ``formula`` is already simplified (so the pruned atoms are in simplest form) --
    which is BCP's invariant. Keys must be booleans occurring only in boolean
    position.
    """
    sub_vars = frozenset(subs)
    simp = get_env().simplifier
    fns = simp.functions
    memo: dict[FNode, FNode] = {}

    def go(f: FNode) -> FNode:
        cached = memo.get(f)
        if cached is not None:
            return cached
        if f.get_free_variables().isdisjoint(sub_vars):
            memo[f] = f
            return f
        if f.is_symbol():
            r = subs.get(f, f)
        else:
            r = fns[f.node_type()](f, [go(a) for a in f.args()])
        memo[f] = r
        return r

    return go(formula)


def iter_unique_subnodes(root: FNode):
    """Yield each distinct subnode of ``root`` exactly once.

    Iterative (explicit worklist) rather than recursive: asserted bodies are
    deep *and* heavily share substructure, so a recursion would both risk a
    ``RecursionError`` on the first descent and re-walk shared subterms a
    tree-exponential number of times. The ``seen`` set memoizes over the DAG;
    the worklist keeps stack depth bounded. This is the lightweight equivalent
    of a ``DagWalker`` for callers that only need to scan nodes (no per-node
    value to compute or rewrite).
    """
    seen: set[FNode] = set()
    stack: list[FNode] = [root]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        yield node
        stack.extend(node.args())


def substitute_no_validate(formula, subs, substituter=None):
    """Apply ``subs`` to ``formula`` skipping pysmt's per-call validation.

    ``FNode.substitute`` (i.e. ``Substituter.substitute``) re-validates *every*
    entry of ``subs`` on *every* call -- ``k.is_term()``, ``v.is_term()``,
    ``k in manager``, ``v in manager`` -- which is ``O(|subs|)`` before any work
    is done. Applying a large ``subs`` to many formulas in a loop is then
    quadratic and can dominate runtime (see ``boolean_propagate`` and
    ``simplify_model``). Our keys and values are always valid terms in the
    active manager, so we drive the walker directly and skip the loop.

    Pass ``substituter`` to reuse a configured instance (e.g. one with an
    overridden ``walk_forall``); otherwise the environment's shared substituter
    is used. Behaviour is otherwise identical to ``substituter.substitute``.
    """
    substituter = substituter if substituter is not None else get_env().substituter
    return substituter.walk(formula, substitutions=subs, interpretations={})

def strip_prefix_from_vars(f: FNode, prefix: str) -> FNode:
    if f is None:
        return None
    if isinstance(f, list):
        return [strip_prefix_from_vars(x, prefix) for x in f]
    subs: dict[FNode, FNode] = {}
    for sym in f.get_free_variables():
        if not sym.is_symbol():
            continue
        n = sym.symbol_name()
        nn = n[len(prefix) :] if n.startswith(prefix) else n
        if nn != n:
            subs[sym] = Symbol(nn, sym.symbol_type())
    return f.substitute(subs) if subs else f


def linear_form(e: FNode):
    """``e`` as ``({symbol: coeff}, const)``, or ``None`` if not linear."""
    terms: dict = {}
    const = 0

    def add(c: int, node: FNode) -> bool:
        nonlocal const
        if node.is_int_constant():
            const += c * node.constant_value()
            return True
        if node.is_symbol():
            terms[node] = terms.get(node, 0) + c
            return True
        if node.is_plus():
            return all(add(c, a) for a in node.args())
        if node.is_minus():
            return add(c, node.arg(0)) and add(-c, node.arg(1))
        if node.is_times():
            consts = [a for a in node.args() if a.is_int_constant()]
            rest = [a for a in node.args() if not a.is_int_constant()]
            k = 1
            for cc in consts:
                k *= cc.constant_value()
            if len(rest) == 1:
                return add(c * k, rest[0])
            if not rest:
                const += c * k
                return True
        return False

    return (terms, const) if add(1, e) else None


def with_comment(f: FNode, comment: str) -> FNode:
    """Set the comment of f to comment."""
    if f is None:
        return None
    if SUPPORTS_COMMENTS:
        setattr(f, "comment", comment)
    return f


def keep_comment(new: FNode, old: FNode) -> FNode:
    """Copy the comment from old to new."""
    if SUPPORTS_COMMENTS and hasattr(old, "comment"):
        setattr(new, "comment", old.comment)
    return new


def attach_comment(comment: str):
    """
    Decorator that attaches a comment to the result of a function.
    The comment string can use all arguments and keyword arguments of the
    function via the format string syntax.
    """

    def inner(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            res = func(*args, **kwargs)
            if res is None:
                return None
            if isinstance(res, GeneratorType):
                return (with_comment(f, comment.format(*args, **kwargs)) for f in res)
            return with_comment(res, comment.format(*args, **kwargs))

        return wrapper

    return inner


class ConsequenceKind(enum.Enum):
    """What a consequence *is*, attached by whoever produced it.

    Consumers that need a particular class of granted fact (rather than all of
    them) select on this instead of guessing. Guessing was the alternative and
    both forms of it are bad: matching the emitter's comment only works with the
    local pysmt comment patch, and pattern-matching the formula (e.g. "the one
    carrying the literal 255") silently rots as the encoders change.
    """

    UNTAGGED = "untagged"
    MEMORY_RECV_BYTES = "memory-recv-bytes"
    MEMORY_TIMESTAMP_BOUNDS = "memory-timestamp-bounds"
    RANGE_INFERENCE = "range-inference"


class Consequence(NamedTuple):
    """A granted fact plus its kind. See ``ConsequenceKind``.

    Producers may append either a ``Consequence`` or a bare ``FNode`` to their
    ``consequences`` list; ``as_consequence`` normalises the latter to
    ``UNTAGGED``, so tagging is opt-in per producer.
    """

    kind: ConsequenceKind
    formula: FNode


def as_consequence(c) -> Consequence:
    """Normalise a bare ``FNode`` to an ``UNTAGGED`` ``Consequence``."""
    return c if isinstance(c, Consequence) else Consequence(ConsequenceKind.UNTAGGED, c)


def consequence_formulas(cs: Iterable) -> list[FNode]:
    """The formulas of ``cs``, accepting tagged and bare entries alike.

    Simplified, which decides constant guards: a disabled (``mult = 0``) memory row's
    byte grant folds to true and drops out. A symbolic mult keeps its guard.
    """
    return list(
        without_trues(
            keep_comment(f.simplify(), f)
            for f in (as_consequence(c).formula for c in cs)
            if f is not None
        )
    )


def consequences_of_kind(cs: Iterable, *kinds: ConsequenceKind) -> list[FNode]:
    """Formulas of ``cs`` whose kind is one of ``kinds``."""
    wanted = frozenset(kinds)
    return consequence_formulas(c for c in map(as_consequence, cs) if c.kind in wanted)


def without_true_consequences(cs: Iterable) -> list[Consequence]:
    """``without_trues`` for consequences: normalises and drops None/true."""
    out = []
    for c in cs:
        n = as_consequence(c)
        if n.formula is not None and not n.formula.is_true():
            out.append(n)
    return out


def without_trues(fs: Iterable[FNode]) -> Iterable[FNode]:
    """Filter out `None` and trivially-true formulas from an iterable."""
    return filter(lambda x: x is not None and not x.is_true(), fs)


def as_constant(f: FNode) -> Any:
    """Return a Python value for constants, otherwise a stable string representation."""
    if f.is_constant():
        return f.constant_value()
    return str(f)


def to_nice_model(model: Any) -> dict[str, Any]:
    """Convert a solver model into a JSON-friendly dict, optionally stripping symbol prefixes."""
    return {
        str(k): as_constant(v)
        for k, v in sorted(model, key=lambda x: str(x))
        if not v.is_array_value() and not v.is_array_op()
    }


@attach_comment("BASIC RANGE axiom for {0}")
def field_symbol(sym: FNode) -> FNode:
    """Constrain `sym` to lie in the field range (0 ... p-1) for the configured modulus."""
    return And(LE(Int(0), sym), LT(sym, Int(ARGS().field_type.value)))


def MultiArrayType(index, width, value) -> FNode:
    """Construct an `ArrayType` nested `width` times (i.e. a multi-dimensional array type)."""
    if width > 0:
        return ArrayType(index, MultiArrayType(index, width - 1, value))
    return value


class NameOrIdGenerator:
    """Stable naming helper: use symbol/constant names, else assign fresh ids to compound terms."""

    def __init__(self):
        """Initialize an empty mapping from expressions to stable integer ids."""
        self.mapping = {}

    def __call__(self, x: FNode) -> str:
        """Return `str(x)` for symbols/constants, else a stable fresh id for compound terms."""
        if x.is_constant() or x.is_symbol():
            return str(x)
        return self.mapping.setdefault(x, len(self.mapping))


class VarBaseFormulaSelector:
    """Index formulas by free variables to support quick relevance selection (shallow/deep)."""

    def __init__(self, formulae: list[FNode]):
        """Index formulas by free variables to support shallow/deep relevance selection."""
        var_to_formulae = {f: f.get_free_variables() for f in formulae}
        self.lookup = {
            v: frozenset(f for f in var_to_formulae if v in var_to_formulae[f])
            for v in frozenset.union(*var_to_formulae.values())
        }

    def resolve_shallow(self, vars: list[FNode]) -> FNode:
        """Return formulas that mention any of `vars` (one-hop variable-to-formula lookup)."""
        if not vars:
            return frozenset()
        return frozenset.union(*[self.lookup[v] for v in vars])

    def resolve_deep(self, vars: list[FNode]) -> FNode:
        """Return a fixpoint of formulas reachable via shared variables starting from `vars`."""
        if not vars:
            return frozenset()
        last = frozenset()
        cur = self.resolve_shallow(vars)
        while cur != last:
            last = cur
            vars = vars | frozenset.union(*[f.get_free_variables() for f in last])
            cur = self.resolve_shallow(vars)
        return cur

    def resolve_shallow_for(self, fs: list[FNode]) -> FNode:
        """Shallow-resolve formulas relevant to the free variables of formulas `fs`."""
        return self.resolve_shallow(
            frozenset.union(*[f.get_free_variables() for f in fs])
        )

    def resolve_deep_for(self, fs: list[FNode]) -> FNode:
        """Deep-resolve formulas relevant to the free variables of formulas `fs`."""
        return self.resolve_deep(frozenset.union(*[f.get_free_variables() for f in fs]))


class GenericInterpreter(FunctionInterpretation):
    """Provides a generic interpreter for an uninterpreted function symbol.
    Supports both evaluation of concrete arguments and symbolic simplification."""

    def __init__(self, fsym, f):
        """Set up the interpreter. `f` can be a simple concrete evaluator, or a pair of a concrete evaluator and a symbolic simplifier."""
        self.fsym = fsym
        if isinstance(f, tuple):
            self.concrete, self.symbolic = f
        elif callable(f):
            self.concrete = f
            self.symbolic = None
        else:
            logging.error(f"can not use {f} as interpreter for {fsym}")

    def interpret(self, env, args: list[FNode]) -> FNode:
        """Interpret on constants, else use symbolic simplification if available, else keep UF call."""
        if all(arg.is_constant() for arg in args):
            return self.concrete(*[arg.constant_value() for arg in args])
        if self.symbolic is not None:
            if res := self.symbolic(*args):
                return res
        return Function(self.fsym, args)


def partial_evaluate(f: FNode, model: dict[str, Any], interpreters):
    """Partially evaluate a formula by substituting model values and UF interpretations. Run up to three iterations."""
    substitutions = {}
    for name, value in model.items():
        if isinstance(value, bool):
            substitutions[Symbol(name, BOOL)] = Bool(value)
        elif isinstance(value, int):
            substitutions[Symbol(name, INT)] = Int(value)
    interpretations = {
        sym: GenericInterpreter(sym, f) for sym, f in interpreters.items()
    }

    refresh = _refresh_formula if not substitutions and not interpretations else None
    last = None
    cnt = 3
    while last != f and cnt > 0 and not f.is_constant():
        last = f
        if refresh is not None:
            f = refresh(f).simplify()
        else:
            f = f.substitute(substitutions, interpretations).simplify()
        cnt -= 1
    
    if f.is_int_constant():
        f = Int(f.constant_value() % ARGS().field_type.value)

    return f


def find_unique_solution(s: Solver, f: FNode) -> Optional[dict[str, int]]:
    """Return a unique satisfying assignment for `f` (over its free vars), or None if non-unique/unsat."""
    try:
        s.push()
        s.add_assertion(f)
        if s.solve():
            model = s.get_model()
            vars = f.get_free_variables()
            s.add_assertion(Or(*[Not(Equals(v, c)) for v, c in model if v in vars]))
            res = s.solve()
            s.pop()
            if res:
                return None
            return {v: c for v, c in model if v in vars}

        s.pop()
        return None
    except:
        return None


_simplify_and_check_dump_i = itertools.count()


def simplify_and_check(
    formula: FNode,
    *,
    simplify_timeout: float,
    check_timeout: float,
    tactic: str,
    smt_dump_base: Path | None = None,
    parent_action=None,
) -> bool | None:
    """``True`` / ``False`` / ``None`` (inconclusive) for PySMT-validity of ``formula``."""
    from ..checker import check_smt_script
    from ..report.action import Action
    from ..simplifier import simplify_smt_script

    smt = convert_to_smt_script(Not(formula))
    if not hasattr(ARGS(), "pretty"):
        ARGS().pretty = False
    if not hasattr(ARGS(), "dump_steps"):
        ARGS().dump_steps = False
    if not hasattr(ARGS(), "dump_model"):
        ARGS().dump_model = None
    prev_pretty = ARGS().pretty
    prev_dump_steps = ARGS().dump_steps
    prev_dump_model = ARGS().dump_model
    try:
        ARGS().pretty = False
        ARGS().dump_steps = False
        root_cm = (
            parent_action.action("simplify-and-check")
            if parent_action is not None
            else Action("simplify-and-check")
        )
        with root_cm as check_action:
            smt, _ = simplify_smt_script(
                smt,
                tactic=tactic,
                timeout=float(simplify_timeout),
                parent_action=check_action,
            )
            if smt_dump_base is not None and getattr(ARGS(), "dump_smt", False):
                n = next(_simplify_and_check_dump_i)
                dump_path = Path(smt_dump_base).with_suffix(f".memory-align-{n:04d}.smt2")
                dump_path.parent.mkdir(parents=True, exist_ok=True)
                with open_file(dump_path, "w") as f:
                    serialize_smtlib(smt, f)
                logging.info("dumped simplify_and_check pre-check SMT2 to %s", dump_path)
            ARGS().dump_model = None
            match check_smt_script(
                smt, check_action, input_for_log=None, check_timeout=check_timeout
            ):
                case "unsat":
                    return True
                case "sat":
                    return False
                case _:
                    return None
    finally:
        ARGS().pretty = prev_pretty
        ARGS().dump_steps = prev_dump_steps
        ARGS().dump_model = prev_dump_model
