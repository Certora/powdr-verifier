"""Canonicalize uninterpreted bitwise-table application arguments (``ufnorm``).

``z3-solve-eqs`` eliminates variables with non-unit coefficients by
introducing ``mod!``/``div!`` witness definitions and substitutes through
uf arguments — after it, the same table application appears with
side-dependently normalized arguments (raw linear combos carrying
``+P*mod!k`` summands). EUF congruence can then no longer match the
premise/goal twins of an inlining step, and every match needs an integer
quotient side-proof nested inside the xor chains (measured on 2100224:
5242 witness-form uf args vs 0 canonical, and the whole hard-disjunct
family had exactly this shape).

This pass restores canonical arguments::

    f(..., a, ...)  ->  f(..., (mod a' P), ...)

where ``a'`` is ``a``'s linear form with coefficients reduced mod P —
dropping P-multiple summands, which is exactly the ``mod!`` witnesses —
terms sorted by symbol name. Each rewritten application gets a ground
connection axiom ``f(orig) = f(canon)`` asserted top-level. The tables are
only ever applied to field-reduced values, so mod-P invariance of the uf
is a granted environment fact (same epistemic status as assume_bytes /
TS_BOUND), and under the asserted instance the rewrite is a pure
equational step — refutation-sound.
"""
import logging

from ..smt.utils import *
from ..utils.stats import stats_dump

UF_NAMES = frozenset(["uf_xor", "uf_and", "uf_or"])


def _linear_atoms(e: FNode) -> tuple[dict[FNode, int], int] | None:
    """``e`` as ``({atom: coeff}, const)`` treating non-arithmetic subterms
    (uf applications, mod terms, ...) as atoms — a generalization of
    ``linear_form``, which only knows symbols and gives up on the nested
    xor-chain arguments."""
    terms: dict[FNode, int] = {}
    const = 0

    def add(c: int, node: FNode) -> bool:
        nonlocal const
        if node.is_int_constant():
            const += c * node.constant_value()
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
        # atom: symbol, uf application, mod term, ...
        terms[node] = terms.get(node, 0) + c
        return True

    return (terms, const) if add(1, e) else None


def _canon_arg(arg: FNode, p: int) -> FNode | None:
    """Canonical form of a uf argument, or ``None`` if already canonical.

    Bare symbols and reduced constants are canonical as-is. Everything else
    canonicalizes to ``(mod linear' P)`` with coefficients in ``[0, P)``
    (zero-mod-P coefficients dropped — exactly the ``P*mod!k`` witness
    summands) and atoms sorted; an argument the linear decomposition cannot
    handle is left alone.
    """
    if arg.is_symbol():
        return None
    if arg.is_int_constant():
        v = arg.constant_value() % p
        return None if v == arg.constant_value() else Int(v)
    inner = arg
    if arg.node_type() == operators.MOD:
        modulus = arg.arg(1)
        if not (modulus.is_int_constant() and modulus.constant_value() == p):
            return None  # foreign modulus: leave alone
        inner = arg.arg(0)
    lf = _linear_atoms(inner)
    if lf is None:
        return None
    terms, const = lf
    parts = []
    for atom in sorted(terms, key=str):
        c = terms[atom] % p
        if c == 0:
            continue
        parts.append(atom if c == 1 else Times(Int(c), atom))
    if const % p != 0:
        parts.append(Int(const % p))
    canon_inner = Plus(parts) if len(parts) > 1 else (parts[0] if parts else Int(0))
    canon = wrap_mod(canon_inner, Int(p))
    return None if canon == arg else canon


def simplify_ufnorm(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    p = ARGS().field_type.value
    mgr = get_env().formula_manager
    memo: dict[FNode, FNode] = {}
    axioms: dict[FNode, FNode] = {}
    stats = {"apps_seen": 0, "apps_canonicalized": 0}

    def rewrite(root: FNode) -> FNode:
        stack = [root]
        while stack:
            n = stack[-1]
            if n in memo:
                stack.pop()
                continue
            pending = [a for a in n.args() if a not in memo]
            if pending:
                stack.extend(pending)
                continue
            stack.pop()
            args = tuple(memo[a] for a in n.args())
            if (
                n.is_function_application()
                and n.function_name().symbol_name() in UF_NAMES
            ):
                stats["apps_seen"] += 1
                base = (
                    n
                    if args == tuple(n.args())
                    else Function(n.function_name(), list(args))
                )
                canon_args = [_canon_arg(a, p) for a in base.args()]
                if any(c is not None for c in canon_args):
                    stats["apps_canonicalized"] += 1
                    new_args = [
                        c if c is not None else a
                        for c, a in zip(canon_args, base.args())
                    ]
                    new_app = Function(n.function_name(), new_args)
                    if base not in axioms and base != new_app:
                        axioms[base] = with_comment(
                            Equals(base, new_app),
                            "UFNORM: table mod-P invariance (granted)",
                        )
                    memo[n] = new_app
                    continue
                memo[n] = base
            elif not n.args() or args == tuple(n.args()):
                memo[n] = n
            else:
                memo[n] = mgr.create_node(
                    node_type=n.node_type(), args=args, payload=n._content.payload
                )
        return memo[root]

    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = rewrite(cmd.args[0])

    if axioms:
        axiom_cmds = [
            script.SmtLibCommand(name="assert", args=[ax])
            for ax in axioms.values()
        ]
        output = []
        inserted = False
        for cmd in smt_script.commands:
            if not inserted and cmd.name == "assert":
                output.extend(axiom_cmds)
                inserted = True
            output.append(cmd)
        smt_script.commands = output

    record = {**stats, "connection_axioms_added": len(axioms)}
    if subaction is not None:
        subaction += record
    stats_dump("ufnorm", record)
    logging.info("ufnorm: %s", record)
    return smt_script
