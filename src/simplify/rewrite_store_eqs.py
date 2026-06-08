"""Static reduction of array-equality `(= a b)` through store / const-array chains.

For an equality between two array-typed expressions where the structure
is a chain of stores (or const-arrays) at constant indices, the
equality decomposes into a conjunction of inner value equalities plus
an equality on the surviving bases. The reduction is exact (sound and
preserves the constraint) and produces a ground form with no
remaining array-store layer.

## Reduction rules (informal)

* `(= a a)` → `True`
* `(= (store a k v) (store a k v'))` → `(= v v')`
* `(= (store a k v) (store a k' v'))` with constant `k ≠ k'`:
  → `(and (= v (select a k))         ;; LHS at k = v;  RHS at k = a[k]
          (= (select a k') v'))`     ;; LHS at k' = a[k']; RHS at k' = v'
  (bases agree on the unaffected positions trivially)
* `(= (store a k v) b)` with constant `k`:
  → `(and (= v <b read at k>)
          (= a <b with store at k peeled if applicable, else b>))`
  recursively.
* `(= ((as const T) v1) ((as const T) v2))` → `(= v1 v2)`
* For nested array-typed values (inner arrays), the produced inner
  equality is again array-typed and gets the same recursive treatment.
  At scalar leaves the result becomes a plain `Equals` (or `Iff` for
  Bool element type).

When the bases of two store-chains aren't structurally identical, the
fallback `(= base_a base_b)` is kept as residue — z3 still needs to
prove (or refute) that.

## Pipeline placement

After `solve_store_eqs` (which inlines chain defs producing the deep
store-on-store-on-base shape) and before `flatten_outer_array` (whose
hard-fail contract requires no 2D arrays remain). The reducer
collapses the deeply-nested 2D store equalities to scalar form so
flatten has nothing 2D to dissect.
"""
from pysmt import operators as op

from ..smt.utils import *


def _canon_arith(mgr, expr: FNode, mod_p: FNode | None = None) -> FNode:
    """Return ``expr`` rewritten to a canonical arithmetic form for the
    purpose of comparing store-index expressions. Recursive.

    Rules applied:
      1. Sort commutative ``Plus`` / ``Times`` operands by a stable key
         so ``(* x c)`` and ``(* c x)`` canonicalize identically.
      2. ``(mod (mod x p) p) → (mod x p)``.
      3. When inside an outer ``(mod _ p)`` (signalled by ``mod_p`` being
         set), strip every ``(mod _ p)`` wrapper encountered on Plus /
         Times operands transitively — the distributive law of mod over
         arithmetic.

    These suffice for the difference observed between the two sides of
    flatten-produced store equalities in the keccak case:

    * `((x * 65536) + y) % p`
    * `((65536 * (x % p)) + (y % p)) % p`

    Both canonicalize to the same FNode under hash-consing.
    """
    nt = expr.node_type()

    if nt == op.MOD:
        modulus = expr.arg(1)
        inner_canon = _canon_arith(mgr, expr.arg(0), mod_p=modulus)
        # Mod(Mod(x, p), p) → Mod(x, p)
        if inner_canon.node_type() == op.MOD and inner_canon.arg(1) == modulus:
            return mgr.Mod(inner_canon.arg(0), modulus)
        return mgr.Mod(inner_canon, modulus)

    if nt == op.PLUS or nt == op.TIMES:
        args = [_canon_arith(mgr, c, mod_p=mod_p) for c in expr.args()]
        # Under an outer Mod(_, mod_p), inner Mod(_, mod_p) wrappers on
        # Plus / Times operands are redundant per the distributive law.
        if mod_p is not None:
            args = [
                a.arg(0) if a.node_type() == op.MOD and a.arg(1) == mod_p else a
                for a in args
            ]
        args = sorted(args, key=_sort_key)
        return mgr.Plus(*args) if nt == op.PLUS else mgr.Times(*args)

    # Leaf or non-arithmetic op: return original (no canonicalization
    # rule applies). We don't generically rebuild children for shapes
    # like Select, Ite, etc. — the index expressions we care about are
    # arithmetic chains rooted at Plus / Times / Mod.
    return expr


def _sort_key(node: FNode):
    """Stable sort key for canonicalizing commutative operands. Constants
    last, then by node-type, then by string repr."""
    is_const = node.is_int_constant() or node.is_real_constant()
    return (0 if not is_const else 1, node.node_type(), str(node))


def _eq_typed(mgr, a: FNode, b: FNode) -> FNode:
    """Equals for non-Bool, Iff for Bool. pysmt forbids Equals on Bool."""
    if a.get_type().is_bool_type():
        return mgr.Iff(a, b)
    return mgr.Equals(a, b)


def _read(mgr, expr: FNode, idx: FNode) -> FNode:
    """Return ``(select expr idx)`` simplified through any store chain
    when both expr's store indices and `idx` are constant. Falls back
    to a literal Select for shapes we can't statically resolve.
    """
    if not idx.is_int_constant():
        return mgr.Select(expr, idx)
    while expr.node_type() == op.ARRAY_STORE:
        e_idx = expr.arg(1)
        if not e_idx.is_int_constant():
            return mgr.Select(expr, idx)
        if e_idx.constant_value() == idx.constant_value():
            return expr.arg(2)
        expr = expr.arg(0)
    if expr.node_type() == op.ARRAY_VALUE:
        return expr.array_value_default()
    return mgr.Select(expr, idx)


def _reduce(mgr, a: FNode, b: FNode) -> FNode:
    """Return a simpler-but-equivalent formula for ``(= a b)``. Recurses
    into nested array equalities."""
    if a == b:
        return mgr.TRUE()

    nt_a, nt_b = a.node_type(), b.node_type()

    # Both stores: structurally peel.
    if nt_a == op.ARRAY_STORE and nt_b == op.ARRAY_STORE:
        a_base, a_idx, a_val = a.arg(0), a.arg(1), a.arg(2)
        b_base, b_idx, b_val = b.arg(0), b.arg(1), b.arg(2)

        # Same index expression (constant OR same variable FNode): values
        # forced equal, bases must agree everywhere else. The rule
        # `(= (store a k v1) (store a k v2)) ↔ (= v1 v2)` holds regardless
        # of whether `k` is a literal constant, as long as both sides
        # share the same index FNode (or canonicalize to the same FNode
        # under the small arithmetic canonicalizer for cases like
        # operand commutativity and redundant mod wrappers).
        if a_idx == b_idx or _canon_arith(mgr, a_idx) == _canon_arith(mgr, b_idx):
            val_eq = _reduce(mgr, a_val, b_val) \
                if a_val.get_type().is_array_type() \
                else _eq_typed(mgr, a_val, b_val)
            base_eq = _reduce(mgr, a_base, b_base)
            return _and(mgr, val_eq, base_eq)

        if a_idx.is_int_constant() and b_idx.is_int_constant():
            # Different constant indices.
            # LHS read at a_idx = a_val; RHS read at a_idx = b read at a_idx.
            # LHS read at b_idx = a read at b_idx; RHS read at b_idx = b_val.
            # Elsewhere: a_base read = b_base read → reduces to (= a_base b_base).
            rb_at_a = _read(mgr, b, a_idx)
            ra_at_b = _read(mgr, a, b_idx)
            e1 = _reduce(mgr, a_val, rb_at_a) \
                if a_val.get_type().is_array_type() \
                else _eq_typed(mgr, a_val, rb_at_a)
            e2 = _reduce(mgr, ra_at_b, b_val) \
                if b_val.get_type().is_array_type() \
                else _eq_typed(mgr, ra_at_b, b_val)
            base_eq = _reduce(mgr, a_base, b_base)
            return _and(mgr, e1, e2, base_eq)
        # Different/incomparable variable indices: can't statically reduce.
        return _eq_typed(mgr, a, b)

    # One side store, other non-store: peel the store side.
    if nt_a == op.ARRAY_STORE:
        a_base, a_idx, a_val = a.arg(0), a.arg(1), a.arg(2)
        if a_idx.is_int_constant():
            rb_at_idx = _read(mgr, b, a_idx)
            e1 = _reduce(mgr, a_val, rb_at_idx) \
                if a_val.get_type().is_array_type() \
                else _eq_typed(mgr, a_val, rb_at_idx)
            base_eq = _reduce(mgr, a_base, b)
            return _and(mgr, e1, base_eq)
        return _eq_typed(mgr, a, b)

    if nt_b == op.ARRAY_STORE:
        b_base, b_idx, b_val = b.arg(0), b.arg(1), b.arg(2)
        if b_idx.is_int_constant():
            ra_at_idx = _read(mgr, a, b_idx)
            e1 = _reduce(mgr, ra_at_idx, b_val) \
                if b_val.get_type().is_array_type() \
                else _eq_typed(mgr, ra_at_idx, b_val)
            base_eq = _reduce(mgr, a, b_base)
            return _and(mgr, e1, base_eq)
        return _eq_typed(mgr, a, b)

    # Both const-arrays: reduce to value equality.
    if nt_a == op.ARRAY_VALUE and nt_b == op.ARRAY_VALUE:
        va, vb = a.array_value_default(), b.array_value_default()
        if va.get_type().is_array_type():
            return _reduce(mgr, va, vb)
        return _eq_typed(mgr, va, vb)

    # One side const-array, other a bare symbol: leave alone — this is
    # a definitional equality for solve_store_eqs / define_inner_array.
    # Default: structurally irreducible, keep the array equality.
    return _eq_typed(mgr, a, b)


def _and(mgr, *args: FNode) -> FNode:
    """Build an And, folding out True conjuncts. Returns True for empty,
    the lone conjunct for singletons."""
    kept = [a for a in args if not a.is_true()]
    if not kept:
        return mgr.TRUE()
    if len(kept) == 1:
        return kept[0]
    return mgr.And(*kept)


class _StoreEqReducer(IdentityDagWalker):
    """Walks the formula, reducing array-typed Equals via static
    store-chain unfolding. Also folds ``True``/``False`` through And/Or/Not
    so that all-True / all-False reductions propagate cleanly.
    """

    def __init__(self, env=None):
        super().__init__(env=env)
        self.reductions = 0

    def walk_equals(self, formula, args, **kwargs):
        a, b = args[0], args[1]
        if a.get_type().is_array_type():
            new = _reduce(self.mgr, a, b)
            if new is not formula:
                self.reductions += 1
            return new
        return self.mgr.Equals(*args)

    def walk_array_select(self, formula, args, **kwargs):
        """Static select-over-store: ``(select (store a k v) k')`` with
        both indices constant resolves to ``v`` (when ``k == k'``) or
        ``(select a k')`` (when different). Also unwraps ``(as const T)``
        bases to their default value."""
        arr, idx = args[0], args[1]
        if idx.is_int_constant():
            new = _read(self.mgr, arr, idx)
            if new is not formula and new.node_type() != op.ARRAY_SELECT:
                self.reductions += 1
            elif new.node_type() == op.ARRAY_SELECT and (
                new.arg(0) is not arr or new.arg(1) is not idx
            ):
                self.reductions += 1
            return new
        return self.mgr.Select(arr, idx)

    def walk_and(self, formula, args, **kwargs):
        kept = [x for x in args if not x.is_true()]
        if any(x.is_false() for x in kept):
            return self.mgr.FALSE()
        if not kept:
            return self.mgr.TRUE()
        if len(kept) == 1:
            return kept[0]
        return self.mgr.And(*kept)

    def walk_or(self, formula, args, **kwargs):
        kept = [x for x in args if not x.is_false()]
        if any(x.is_true() for x in kept):
            return self.mgr.TRUE()
        if not kept:
            return self.mgr.FALSE()
        if len(kept) == 1:
            return kept[0]
        return self.mgr.Or(*kept)

    def walk_not(self, formula, args, **kwargs):
        a = args[0]
        if a.is_true():
            return self.mgr.FALSE()
        if a.is_false():
            return self.mgr.TRUE()
        return self.mgr.Not(a)


def simplify_rewrite_store_eqs(
    smt_script: script.SmtLibScript, subaction=None
) -> script.SmtLibScript:
    """See module docstring."""
    walker = _StoreEqReducer(env=get_env())

    rewrites = 0
    asserts_dropped = 0
    new_commands: list = []
    for cmd in smt_script.commands:
        if cmd.name == "assert":
            old = cmd.args[0]
            new = walker.walk(old)
            if new.is_true():
                asserts_dropped += 1
                continue
            if new is not old:
                cmd.args[0] = keep_comment(new, old)
                rewrites += 1
        new_commands.append(cmd)
    smt_script.commands = new_commands

    logging.info(
        f"rewrite_store_eqs: reductions={walker.reductions} "
        f"asserts_rewritten={rewrites} asserts_dropped={asserts_dropped}"
    )
    if subaction is not None:
        subaction += {
            "reductions": walker.reductions,
            "asserts_rewritten": rewrites,
            "asserts_dropped": asserts_dropped,
        }
    return smt_script
