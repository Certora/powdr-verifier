"""Top-level equality elimination by substitution.

Free variables in an SMT-LIB script are implicitly existentially
quantified at the top level. For each ``(assert … (= a b) …)`` in
purely conjunctive context where one side is a declared symbol ``x``
not appearing in the other side ``e``, the existential witness for
``x`` is ``e``; we substitute ``x := e`` throughout, drop the equality,
and drop ``x``'s declaration. This is the standard
quantifier-elimination step for free variables, generalized to arrays.

Targets the pin equalities ``(= before-memory-N-X after-memory-N-X)``
emitted by ``array_subst`` (and the 1D versions exposed by
``flatten_outer_array``) — collapses the dual chain into one and lets
downstream simplifiers (define_inner_array, z3-propagate-values) work
on a cleaner formula.

Conjunctive context — we descend through nested ``(and …)`` chains.
A candidate equality must be reachable from the top of an assert
through only And nodes; descent stops at any other operator
(disjunction, negation, implication, ite, quantifier), which would
make the equality conditional and unsound to eliminate.

Eligibility — an equality ``(= a b)`` is eligible iff
1. one side is a declared symbol ``x``;
2. the other side ``e`` does not mention ``x`` (acyclic);
3. ``e`` contains no ``store`` constructor — store-RHS equalities are
   defining equalities for a different pass (``define_inner_array``).

Const-array ``((as const T) v)`` on the RHS is allowed: it's a
first-class constant value (like a scalar 5), not a defining store.

Heuristic when both sides are declared symbols: eliminate the one
declared *later* in the script. In keccak the pins are
``(= before-X after-X)`` with ``after`` declared later, so ``after-``
gets substituted with ``before-`` — keeping the original-state name.

After substitution any ``(= e e)`` and singleton/empty ``(and …)``
left behind by the substitution are folded out by ``_FoldRefl``.
"""
from pysmt import substituter
from pysmt import operators as op

from ..smt.utils import *


def _contains_array_store(expr: FNode) -> bool:
    """True iff ``expr`` contains an ARRAY_STORE node anywhere.

    ARRAY_VALUE (``(as const …)``) is NOT a disqualifier — const-arrays
    are first-class constants, treated like scalar constants.
    """
    if expr.node_type() == op.ARRAY_STORE:
        return True
    return any(_contains_array_store(c) for c in expr.args())


def _declared_order(smt_script: script.SmtLibScript) -> dict[str, int]:
    """Map declare-fun symbol name -> first declaration position."""
    out: dict[str, int] = {}
    for i, cmd in enumerate(smt_script.commands):
        if cmd.name == "declare-fun" and cmd.args[0].is_symbol():
            n = cmd.args[0].symbol_name()
            if n not in out:
                out[n] = i
    return out


def _pick_elim_target(
    f: FNode,
    declared: set[str],
    decl_order: dict[str, int],
):
    """Return ``(sym_to_eliminate, value_expr)`` or ``None`` if the equality
    is not eligible per the module docstring."""
    if not f.is_equals():
        return None
    a, b = f.arg(0), f.arg(1)
    fvo = get_env().fvo

    def eligible(sym: FNode, expr: FNode):
        if not sym.is_symbol():
            return False
        if sym.symbol_name() not in declared:
            return False
        if sym in fvo.get_free_variables(expr):
            return False
        if _contains_array_store(expr):
            return False
        return True

    a_ok = eligible(a, b)
    b_ok = eligible(b, a)

    if a_ok and b_ok:
        a_pos = decl_order.get(a.symbol_name(), -1)
        b_pos = decl_order.get(b.symbol_name(), -1)
        if a_pos >= b_pos:
            return (a, b)
        return (b, a)
    if a_ok:
        return (a, b)
    if b_ok:
        return (b, a)
    return None


def _find_candidate_in_conjunct(
    node: FNode,
    declared: set[str],
    decl_order: dict[str, int],
):
    """Walk through nested ``(and …)`` to find an eligible equality.
    Returns ``(sym, expr)`` or ``None``. Stops descending at any node
    that isn't And or Equals — so disjunction/negation/ite/quantifier
    block descent and protect conditional equalities."""
    if node.is_equals():
        return _pick_elim_target(node, declared, decl_order)
    if not node.is_and():
        return None
    for child in node.args():
        found = _find_candidate_in_conjunct(child, declared, decl_order)
        if found is not None:
            return found
    return None


class _FoldRefl(IdentityDagWalker):
    """Local simplifier: ``(= e e) -> True`` and ``(and … True …)``
    rewrites. Run after each substitution to clean up the formula
    so subsequent rounds don't re-encounter trivial equalities."""

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


def simplify_solve_eqs(
    smt_script: script.SmtLibScript, subaction=None
) -> script.SmtLibScript:
    """See module docstring."""
    env = get_env()
    decl_order = _declared_order(smt_script)
    declared: set[str] = set(decl_order)

    scalar_elim = 0
    array_elim = 0
    rounds = 0
    self_eq_dropped = 0

    while True:
        # Find a candidate equality in any top-level conjunctive context.
        target = None  # (sym, expr)
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

        sym, expr = target

        # Substitute sym := expr in every assert.
        subs = substituter.MGSubstituter(env)
        subs_map = {sym: expr}
        folder = _FoldRefl(env=env)
        for cmd in smt_script.commands:
            if cmd.name == "assert":
                new = subs.substitute(cmd.args[0], subs_map)
                new = folder.walk(new)
                cmd.args[0] = keep_comment(new, cmd.args[0])

        # Drop sym's declaration and any asserts that became trivially True.
        smt_script.commands = [
            c for c in smt_script.commands
            if not (c.name == "declare-fun"
                    and c.args[0].is_symbol()
                    and c.args[0].symbol_name() == sym.symbol_name())
            and not (c.name == "assert" and c.args[0].is_true())
        ]
        declared.discard(sym.symbol_name())

        if sym.get_type().is_array_type():
            array_elim += 1
        else:
            scalar_elim += 1
        rounds += 1

    # Count remaining array equalities anywhere in the formula.
    array_eqs_remaining = 0
    array_eqs_conjunctive = 0
    array_eqs_under_other = 0

    def count_array_eqs(node, in_conj):
        nonlocal array_eqs_remaining, array_eqs_conjunctive, array_eqs_under_other
        if node.is_equals():
            if node.arg(0).get_type().is_array_type():
                array_eqs_remaining += 1
                if in_conj:
                    array_eqs_conjunctive += 1
                else:
                    array_eqs_under_other += 1
        nt = node.node_type()
        next_in_conj = in_conj and (nt == op.AND)
        # Top-level And keeps in_conj=True; entering any other op disables it.
        for c in node.args():
            count_array_eqs(c, next_in_conj)

    for cmd in smt_script.commands:
        if cmd.name == "assert":
            count_array_eqs(cmd.args[0], True)

    logging.info(
        f"solve_eqs: rounds={rounds} "
        f"scalar={scalar_elim} array={array_elim} "
        f"self_eq_dropped={self_eq_dropped} "
        f"array_eqs_remaining={array_eqs_remaining} "
        f"(conjunctive={array_eqs_conjunctive} other={array_eqs_under_other})"
    )
    if subaction is not None:
        subaction += {
            "rounds": rounds,
            "scalar_eliminations": scalar_elim,
            "array_eliminations": array_elim,
            "self_eq_dropped": self_eq_dropped,
            "array_eqs_remaining": array_eqs_remaining,
            "array_eqs_conjunctive": array_eqs_conjunctive,
            "array_eqs_under_other": array_eqs_under_other,
        }
    return smt_script
