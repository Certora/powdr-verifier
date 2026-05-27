"""Legacy witness simplifications keyed by symbol naming conventions (before/after prefixes)."""
from ..smt.utils import *


def _strip_prefix(name: str) -> str:
    """Strip ``before-`` / ``after-`` prefix from a symbol name."""
    for prefix in ("before-", "after-"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def _symbol_key(f: FNode) -> str | None:
    """Stripped symbol name for ``f``, or ``None`` if not a symbol."""
    if not f.is_symbol():
        return None
    return _strip_prefix(f.symbol_name())


def _int_constant(f: FNode) -> int | None:
    """Integer constant value, or ``None``."""
    if not f.get_type().is_int_type():
        return None
    if not f.is_int_constant():
        return None
    return f.constant_value()


def _flatten(op, f: FNode) -> list[FNode]:
    """Flatten nested ``op`` (e.g. ``PLUS``, ``TIMES``) to a list of leaves."""
    if f.node_type() == op:
        return [x for a in f.args() for x in _flatten(op, a)]
    return [f]


def _split_product(f: FNode) -> tuple[int, list[FNode]]:
    """Split ``Times`` tree into ``(coeff mod field_prime, non-constant factors)``."""
    coeff = 1
    factors = []
    for a in _flatten(operators.TIMES, f):
        if (c := _int_constant(a)) is not None:
            coeff *= c
        else:
            factors.append(a)
    return coeff % ARGS().field_type.value, factors


def _unwrap_zero_mod_eq(f: FNode) -> FNode | None:
    """If ``f`` is ``(= (mod e p) 0)`` with field modulus, return inner ``e``; else LHS of plain ``=``."""
    if not f.is_equals():
        return None
    a, b = f.arg(0), f.arg(1)
    if _int_constant(b) == 0:
        lhs = a
    elif _int_constant(a) == 0:
        lhs = b
    else:
        return None
    if lhs.node_type() == operators.MOD:
        modulus = _int_constant(lhs.arg(1))
        if modulus is None:
            return None
        if modulus != ARGS().field_type.value:
            return None
        return lhs.arg(0)
    return lhs


def _iter_nodes(f: FNode):
    """Depth-first preorder over ``f``."""
    yield f
    for a in f.args():
        yield from _iter_nodes(a)


def _split_symbol_times_sum(parts: list[FNode]) -> tuple[FNode, frozenset[str]] | None:
    """Detect ``sym * (t0 + t1 + …)`` with at least two summands; return ``sym`` and stripped factor names."""
    if len(parts) != 2:
        return None
    for sym, sum_expr in (parts, reversed(parts)):
        if not sym.is_symbol():
            continue
        sum_terms = _flatten(operators.PLUS, sum_expr)
        if len(sum_terms) < 2:
            continue
        names = [_symbol_key(t) for t in sum_terms]
        if any(n is None for n in names):
            continue
        factors = frozenset(names)
        sym_key = _symbol_key(sym)
        if sym_key in factors:
            continue
        return sym, factors
    return None


def _match_collapsed_witness(f: FNode) -> tuple[frozenset[str], str, FNode] | None:
    """Match optimizer-collapsed ``mod``-zero witness; return ``(factor_names, cmp_name, free_var)``."""
    lhs = _unwrap_zero_mod_eq(f)
    if lhs is None:
        return None
    field = ARGS().field_type.value
    free_var = None
    factors = None
    cmp = None
    for term in _flatten(operators.PLUS, lhs):
        coeff, parts = _split_product(term)
        if coeff == 0:
            continue
        if not parts:
            continue
        if coeff in (1, field - 1) and len(parts) == 1 and (name := _symbol_key(parts[0])):
            if cmp is not None:
                return None
            cmp = name
            continue
        if coeff != 1:
            return None
        match = _split_symbol_times_sum(parts)
        if match is None:
            return None
        if factors is not None:
            return None
        free_var, factors = match
    if free_var is None or factors is None or cmp is None:
        return None
    if _symbol_key(free_var) == cmp:
        return None
    return factors, cmp, free_var


def _match_expanded_witness(
    f: FNode,
    qvars: frozenset[FNode],
    candidates: list[tuple[frozenset[str], str, FNode]],
) -> dict[FNode, FNode] | None:
    """Map quantified markers to ``free_var`` when ``f`` matches a collected ``candidates`` pattern."""
    lhs = _unwrap_zero_mod_eq(f)
    if lhs is None:
        return None
    field = ARGS().field_type.value
    cmp = None
    factors = set()
    qmap = {}
    for term in _flatten(operators.PLUS, lhs):
        coeff, parts = _split_product(term)
        if coeff == 0:
            continue
        if not parts:
            continue
        if coeff in (1, field - 1) and len(parts) == 1 and (name := _symbol_key(parts[0])):
            if parts[0] not in qvars:
                if cmp is not None:
                    return None
                cmp = name
                continue
        if coeff != 1 or len(parts) != 2:
            return None
        left, right = parts
        if left in qvars and (factor := _symbol_key(right)):
            qvar = left
        elif right in qvars and (factor := _symbol_key(left)):
            qvar = right
        else:
            return None
        factors.add(factor)
        qmap[qvar] = factor
    if cmp is None or len(qmap) < 2:
        return None
    for candidate_factors, candidate_cmp, free_var in candidates:
        if cmp == candidate_cmp and factors == candidate_factors:
            return {qvar: free_var for qvar in qmap}
    return None


class WitnessSubstituter(IdentityDagWalker):
    """Substitute expanded witness qvars using ``candidates`` from collapsed scan."""

    def __init__(self, candidates, *args, **kwargs):
        """``candidates``: list of ``(factors, cmp, free_var)`` from top-level collapsed matches."""
        super().__init__(*args, **kwargs)
        self.candidates = candidates

    def walk_forall(self, formula, args, **kwargs):
        """Apply substitution map derived from ``_match_expanded_witness`` hits in the body."""
        body = args[0]
        qvars = frozenset(formula.quantifier_vars())
        substitutions = {}
        for node in _iter_nodes(body):
            target = node.arg(0) if node.is_not() else node
            match = _match_expanded_witness(target, qvars, self.candidates)
            if match is not None:
                substitutions.update(match)
        if not substitutions:
            return formula
        body = body.substitute(substitutions)
        qvars = [v for v in formula.quantifier_vars() if v not in substitutions]
        if not qvars:
            return body
        return ForAll(qvars, body)


def simplify_witnesses(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
    """Two-phase: collect collapsed witnesses from asserts, then rewrite matching ``forall`` bodies."""
    candidates = []
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        for node in _iter_nodes(cmd.args[0]):
            match = _match_collapsed_witness(node)
            if match is not None:
                candidates.append(match)
    n_cand = len(candidates)
    if not candidates:
        if subaction is not None:
            subaction += {"witness_candidates": 0}
        return smt_script
    w = WitnessSubstituter(candidates, env=get_env())
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])
    if subaction is not None:
        subaction += {"witness_candidates": n_cand}
    return smt_script
