"""Collapsed-witness skolem contributor.

Replaces the standalone ``witness`` simplifier pass.  The Rust
``rule_based`` optimizer can combine multiple single-occurrence
variables (e.g. ``diff_inv_marker__0..3``) into a single ``free_var``
via its ``SingleOccurrenceVariable`` rule.  The result is a pair of
constraints:

* *Collapsed* (after-side, top-level assertion)::

      free_var * (a_0 + a_1 + ... + a_k) + cmp_coeff * cmp + const = 0

* *Expanded* (before-side, inside the forall body)::

      qvar_0 * a_0 + qvar_1 * a_1 + ... + cmp_coeff * cmp + const = 0

Since substituting every ``qvar_i → free_var`` turns the expanded form
into the collapsed one, ``free_var`` is a valid witness for all of
them.

Usage
-----
1. :func:`collect_candidates` scans top-level assertions for collapsed
   forms (call once from :func:`.skolem.simplify_skolem`).
2. :func:`contribute` pins every qvar that appears in a matching
   expanded form inside the forall body.
"""

from ..smt.utils import *


def _strip_prefix(name: str) -> str:
    for prefix in ("before-", "after-"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def _symbol_key(f: FNode) -> str | None:
    if not f.is_symbol():
        return None
    return _strip_prefix(f.symbol_name())


def _int_constant(f: FNode) -> int | None:
    if not f.get_type().is_int_type():
        return None
    if not f.is_int_constant():
        return None
    return f.constant_value()


def _flatten(op, f: FNode) -> list[FNode]:
    if f.node_type() == op:
        return [x for a in f.args() for x in _flatten(op, a)]
    return [f]


def _split_product(f: FNode) -> tuple[int, list[FNode]]:
    p = ARGS().field_type.value
    coeff = 1
    factors = []
    for a in _flatten(operators.TIMES, f):
        if (c := _int_constant(a)) is not None:
            coeff = (coeff * c) % p
        else:
            factors.append(a)
    return coeff, factors


def _unwrap_zero_mod_eq(f: FNode) -> FNode | None:
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
        if modulus is None or modulus != ARGS().field_type.value:
            return None
        return lhs.arg(0)
    return lhs


def _iter_nodes(f: FNode):
    yield f
    for a in f.args():
        yield from _iter_nodes(a)


def _split_symbol_times_sum(parts: list[FNode]) -> tuple[FNode, frozenset[str]] | None:
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
        if _symbol_key(sym) in factors:
            continue
        return sym, factors
    return None


def _match_collapsed(f: FNode) -> tuple[frozenset[str], str, FNode] | None:
    """Match ``free_var * (a_0 + ... + a_k) + cmp_coeff * cmp [+ const] = 0 (mod p)``."""
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


def collect_candidates(
    smt_script: script.SmtLibScript,
) -> list[tuple[frozenset[str], str, FNode]]:
    """Scan top-level assertions for collapsed-witness patterns."""
    candidates: list[tuple[frozenset[str], str, FNode]] = []
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        for node in _iter_nodes(cmd.args[0]):
            match = _match_collapsed(node)
            if match is not None:
                candidates.append(match)
    return candidates


def contribute(
    skolem_map,
    body: FNode,
    candidates: list[tuple[frozenset[str], str, FNode]],
) -> None:
    """Pin qvars from expanded-witness patterns in the forall *body*.

    For every ``(= (mod (+ qvar_0*a_0 ... cmp_coeff*cmp [+ const]) p) 0)``
    node whose ``(factors, cmp)`` pair matches a collected candidate,
    pin each qvar to the candidate's ``free_var``.
    """
    if not candidates:
        return
    field = ARGS().field_type.value
    qvars = skolem_map.qvars
    unpinned = frozenset(q for q in qvars if not skolem_map.is_pinned(q))
    for node in _iter_nodes(body):
        target = node.arg(0) if node.is_not() else node
        lhs = _unwrap_zero_mod_eq(target)
        if lhs is None:
            continue
        cmp = None
        factors: set[str] = set()
        matched_qvars: list[FNode] = []
        ok = True
        for term in _flatten(operators.PLUS, lhs):
            coeff, parts = _split_product(term)
            if coeff == 0:
                continue
            if not parts:
                continue
            if coeff in (1, field - 1) and len(parts) == 1 and (name := _symbol_key(parts[0])):
                if cmp is not None:
                    ok = False
                    break
                cmp = name
                continue
            if coeff != 1 or len(parts) != 2:
                ok = False
                break
            left, right = parts
            if left in unpinned and (factor := _symbol_key(right)):
                qvar = left
            elif right in unpinned and (factor := _symbol_key(left)):
                qvar = right
            else:
                ok = False
                break
            factors.add(factor)
            matched_qvars.append(qvar)
        if not ok or cmp is None or len(matched_qvars) < 2:
            continue
        for candidate_factors, candidate_cmp, free_var in candidates:
            if cmp == candidate_cmp and factors == candidate_factors:
                for qvar in matched_qvars:
                    skolem_map.pin(qvar, free_var, source="witness")
                break
