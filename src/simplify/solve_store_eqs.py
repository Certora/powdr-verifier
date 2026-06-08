"""Eliminate 2D-array definitional equalities by uniform substitution.

For each top-level conjunctive ``(= arr (store …))`` or
``(= arr ((as const …) …))`` where ``arr`` is a declared **2D** array
symbol (value type is itself an array), substitute ``arr := e``
across all asserts, drop the equality, drop ``arr``'s declaration.

The substitution is sound everywhere because the equality is at top-
level conjunctive context — an unconditional constraint on a free
variable. Uniform substitution propagates the witness consistently.

This is the companion to ``solve_eqs`` for the store-RHS shape, which
``solve_eqs`` deliberately skips. The motivating case: a chain
definition ``(= arr (store …))`` at top level AND a negated form
``(not (= arr (store …)))`` inside ``(or …)`` (conditional context).
After substitution, the same ``(store …)`` expression appears in
both — pysmt's hash-consing makes the resulting ``(= store-expr
store-expr)`` collapse to True via the ``_FoldRefl`` walker. The
negated form becomes False, the disjunct drops from the OR.

**Restricted to 2D arrays only** because that's where the keccak
chain structure lives. 1D arrays defined as ``(= arr-1 (store …))``
are left for ``define_inner_array`` (a later pass) — substituting
them would inline a lot of inner-store machinery and bloat the
formula before flatten can per-k-split the outer layer.

Pipeline placement: AFTER ``solve_eqs`` (which substitutes the
sym=sym pin equalities, making the chain def's LHS the "before-"
canonical symbol that solve_store_eqs then expands), and BEFORE
``flatten_outer_array`` (which would otherwise per-k-split the same
store-RHS into multiple sym=sym 1D fragments that aren't tractable
in disjunctive context).
"""
from pysmt import substituter
from pysmt import operators as op

from ..smt.utils import *


def _is_2d_array_type(t) -> bool:
    """True iff ``t`` is an array whose value type is also an array."""
    if not t.is_array_type():
        return False
    elem_t = t.elem_type if hasattr(t, "elem_type") else t.param_types[0]
    return elem_t.is_array_type()


def _declared_order(smt_script: script.SmtLibScript) -> dict[str, int]:
    out: dict[str, int] = {}
    for i, cmd in enumerate(smt_script.commands):
        if cmd.name == "declare-fun" and cmd.args[0].is_symbol():
            n = cmd.args[0].symbol_name()
            if n not in out:
                out[n] = i
    return out


def _is_store_or_const_array(expr: FNode) -> bool:
    return expr.node_type() in (op.ARRAY_STORE, op.ARRAY_VALUE)


def _pick_2d_target(
    f: FNode, declared: set[str], decl_order: dict[str, int]
):
    """Return ``(sym, store_expr, kind)`` where kind is 'store' or 'const',
    or ``None`` if ineligible."""
    if not f.is_equals():
        return None
    a, b = f.arg(0), f.arg(1)
    fvo = get_env().fvo

    def eligible(sym: FNode, expr: FNode):
        if not sym.is_symbol():
            return False
        if sym.symbol_name() not in declared:
            return False
        if not _is_2d_array_type(sym.get_type()):
            return False
        if not _is_store_or_const_array(expr):
            return False
        if sym in fvo.get_free_variables(expr):
            return False
        return True

    a_ok = eligible(a, b)
    b_ok = eligible(b, a)

    if a_ok and b_ok:
        # Both sides are 2D arrays with store/const RHS — odd but possible.
        # Pick the later-declared one as the substitution target.
        a_pos = decl_order.get(a.symbol_name(), -1)
        b_pos = decl_order.get(b.symbol_name(), -1)
        if a_pos >= b_pos:
            sym, expr = a, b
        else:
            sym, expr = b, a
    elif a_ok:
        sym, expr = a, b
    elif b_ok:
        sym, expr = b, a
    else:
        return None

    kind = "store" if expr.node_type() == op.ARRAY_STORE else "const"
    return (sym, expr, kind)


def _find_candidate_in_conjunct(
    node: FNode, declared: set[str], decl_order: dict[str, int]
):
    """Walk through nested ``(and …)`` to find an eligible 2D defining
    equality. Stops at any non-And, non-Equals node — disjunctive /
    negated / quantified contexts block descent."""
    if node.is_equals():
        return _pick_2d_target(node, declared, decl_order)
    if not node.is_and():
        return None
    for child in node.args():
        found = _find_candidate_in_conjunct(child, declared, decl_order)
        if found is not None:
            return found
    return None


class _FoldRefl(IdentityDagWalker):
    """``(= e e)`` → True; And cleanup of True conjuncts.

    Identical in shape to the walker in solve_eqs.py; copy-pasted for
    milestone-2 focus (refactor into shared helper later if a third
    pass needs it).
    """

    def walk_equals(self, formula, args, **kwargs):
        if args[0] == args[1]:
            return self.mgr.TRUE()
        return self.mgr.Equals(*args)

    def walk_and(self, formula, args, **kwargs):
        kept = [a for a in args if not a.is_true()]
        if not kept:
            return self.mgr.TRUE()
        if len(kept) == 1:
            return kept[0]
        return self.mgr.And(*kept)

    def walk_or(self, formula, args, **kwargs):
        # Drop trivially False disjuncts so that, after substitution
        # collapses (not (= e e)) → (not True) → False, the surrounding
        # (or …) gets cleaned up.
        kept = [a for a in args if not a.is_false()]
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


def simplify_solve_store_eqs(
    smt_script: script.SmtLibScript, subaction=None
) -> script.SmtLibScript:
    """See module docstring."""
    env = get_env()
    decl_order = _declared_order(smt_script)
    declared: set[str] = set(decl_order)

    rounds = 0
    stores_elim = 0
    consts_elim = 0
    asserts_dropped = 0

    while True:
        target = None  # (sym, expr, kind)
        for cmd in smt_script.commands:
            if cmd.name != "assert":
                continue
            found = _find_candidate_in_conjunct(
                cmd.args[0], declared, decl_order
            )
            if found is not None:
                target = found
                break

        if target is None:
            break

        sym, expr, kind = target

        subs = substituter.MGSubstituter(env)
        subs_map = {sym: expr}
        folder = _FoldRefl(env=env)
        for cmd in smt_script.commands:
            if cmd.name == "assert":
                new = subs.substitute(cmd.args[0], subs_map)
                new = folder.walk(new)
                cmd.args[0] = keep_comment(new, cmd.args[0])

        # Drop sym's decl and any asserts that folded to True.
        new_commands = []
        for c in smt_script.commands:
            if c.name == "declare-fun" and c.args[0].is_symbol() \
                    and c.args[0].symbol_name() == sym.symbol_name():
                continue
            if c.name == "assert" and c.args[0].is_true():
                asserts_dropped += 1
                continue
            new_commands.append(c)
        smt_script.commands = new_commands
        declared.discard(sym.symbol_name())

        if kind == "store":
            stores_elim += 1
        else:
            consts_elim += 1
        rounds += 1

    # Count residual array equalities (any (= a b) over array-typed terms).
    array_eqs_remaining = 0

    def count_array_eqs(node):
        nonlocal array_eqs_remaining
        if node.is_equals() and node.arg(0).get_type().is_array_type():
            array_eqs_remaining += 1
        for c in node.args():
            count_array_eqs(c)

    for cmd in smt_script.commands:
        if cmd.name == "assert":
            count_array_eqs(cmd.args[0])

    logging.info(
        f"solve_store_eqs: rounds={rounds} "
        f"stores={stores_elim} consts={consts_elim} "
        f"asserts_dropped={asserts_dropped} "
        f"array_eqs_remaining={array_eqs_remaining}"
    )
    if subaction is not None:
        subaction += {
            "rounds": rounds,
            "stores_eliminated": stores_elim,
            "consts_eliminated": consts_elim,
            "asserts_dropped": asserts_dropped,
            "array_eqs_remaining": array_eqs_remaining,
        }
    return smt_script
