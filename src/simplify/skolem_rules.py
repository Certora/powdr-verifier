"""Rule-derived skolem contributor for OpenVM ``EqualZeroCheck`` patterns.

This module is *not* a standalone simplifier pass anymore; it provides the
:func:`contribute` function used by :mod:`.skolem` to populate a shared
:class:`~.skolem.SkolemMap` with witnesses for ``diff_val`` and
``diff_marker__i`` qvars.

Background
----------
The powdr ``rule_based`` optimizer (see
``powdr/constraint-solver/src/rule_based_optimizer/rules.rs``) recognizes
the constraint set produced by OpenVM's ``LessThan`` core (see
https://github.com/powdr-labs/openvm/blob/4300c42df8f860085b6ca46311f2750a01da3dec/extensions/rv32im/circuit/src/less_than/core.rs)
and replaces it with a much simpler equivalent using a fresh
``inv_of_sum`` witness. The original constraint set has the shape (per
limb ``i in 0..4``)::

    diff_marker__i * (a_i_e * sign + diff_val) = 0           (constr_5..8)
    (1 - sum_dm_>=i) * (-a_i) * sign         = 0             (constr_0..2)
    (1 - sum_dm)     * (1 - a_0) * sign      = 0             (constr_4)
    (1 - sum_dm)     * cmp_result            = 0             (constr_3)
    sum_dm * (sum_dm - 1)                    = 0             (constr_9)
    diff_marker__i * (diff_marker__i - 1)    = 0
    sign = 2 * cmp_result - 1

where ``a_0_e == a_0 - 1`` (i.e. ``c[0] = 1``) and ``a_i_e == a_i`` for
``i in {1,2,3}`` (i.e. ``c[i] = 0``); the constraints encode a 4-limb
less-than against the constant ``c = (1, 0, 0, 0)`` (LSB-first). The
optimizer drops every constraint that connects ``diff_val`` /
``diff_marker__i`` to ``b`` in the *after* system, so the same-name pin
that the verifier would normally use for these qvars is unsound: it
propagates an arbitrary (typically all-zero) after-side witness onto the
before side. This contributor instead computes the canonical OpenVM
witness in terms of ``b`` and registers it with the :class:`SkolemMap`
*before* ``contribute_skolem_names`` runs, so the rule-based witness wins.

For every ``diff_val`` qvar this contributor:

1. Locates the four ``DiffMarkerConstraint`` shapes in the forall body
   (matched in both pre-rewrite ``(= (mod (* dm (+ (* X sign) dv)) p) 0)``
   and post-rewrite ``(or (= dm 0) (= (mod (+ (* X sign) dv) p) 0))``
   forms), indexed by the trailing number of the ``diff_marker__N``
   symbol.
2. Confirms a single shared ``cmp_result``, requires constr_5 to carry
   the ``a_0 - 1`` offset and constr_6..8 to carry no offset.
3. Builds the canonical witness for ``diff_val``::

       diff_val := (c[i] - b[i]) * sign   for the highest i with b[i] != c[i]
                 := 0                     when b == c

   and pins it on the :class:`SkolemMap`.
4. Builds the canonical ``diff_marker__i`` witnesses (``1`` at the
   highest differing limb, ``0`` elsewhere) and pins each that is
   actually quantified by this forall.

All emission (``Not(q = wrap_mod(expr))``) is delegated to the
:class:`SkolemMap`. ``simplify_lift_forall`` later hoists each pin to a
top-level assertion.
"""

from ..smt.utils import *


def _iter_nodes(f: FNode):
    """Yield ``f`` and all of its descendants (DAG traversal, may revisit)."""
    yield f
    for a in f.args():
        yield from _iter_nodes(a)


def _flatten(op, f: FNode) -> list[FNode]:
    """Flatten nested associative ``op`` nodes into a single list of leaves."""
    if f.node_type() == op:
        return [x for a in f.args() for x in _flatten(op, a)]
    return [f]


def _int_constant(f: FNode) -> int | None:
    """Return the Python int value of an integer constant ``FNode`` or ``None``."""
    if not f.get_type().is_int_type():
        return None
    if not f.is_int_constant():
        return None
    return f.constant_value()


def _split_product(f: FNode) -> tuple[int, list[FNode]]:
    """Split a (possibly nested) ``Times`` product into ``(coeff_mod_p, factors)``.

    Numeric factors are accumulated modulo the field prime; the rest are
    returned as the symbolic factor list in their original order.
    """
    p = ARGS().field_type.value
    coeff = 1
    factors = []
    for a in _flatten(operators.TIMES, f):
        c = _int_constant(a)
        if c is not None:
            coeff = (coeff * c) % p
        else:
            factors.append(a)
    return coeff, factors


def _unwrap_zero_mod_eq(f: FNode) -> FNode | None:
    """Recognize ``(= (mod x p) 0)`` (in either argument order) and return ``x``.

    The modulus must equal the configured field prime; anything else returns
    ``None``.
    """
    if not f.is_equals():
        return None
    a, b = f.arg(0), f.arg(1)
    if _int_constant(b) == 0:
        lhs = a
    elif _int_constant(a) == 0:
        lhs = b
    else:
        return None
    if lhs.node_type() != operators.MOD:
        return None
    modulus = _int_constant(lhs.arg(1))
    if modulus != ARGS().field_type.value:
        return None
    return lhs.arg(0)


def _match_sign(f: FNode) -> FNode | None:
    """Match the ``sign = 2*cmp_result - 1`` factor and return the ``cmp_result`` symbol.

    The expected shape is a sum of exactly one numeric constant equal to
    ``-1 mod p`` and one term ``2 * cmp`` where ``cmp`` is a symbol.
    """
    p = ARGS().field_type.value
    terms = _flatten(operators.PLUS, f)
    if len(terms) != 2:
        return None
    const_total = 0
    nonconst = None
    for t in terms:
        c = _int_constant(t)
        if c is not None:
            const_total = (const_total + c) % p
        else:
            if nonconst is not None:
                return None
            nonconst = t
    if nonconst is None:
        return None
    if const_total != (p - 1) % p:
        return None
    coeff, factors = _split_product(nonconst)
    if coeff != 2 or len(factors) != 1:
        return None
    cmp_sym = factors[0]
    if not cmp_sym.is_symbol():
        return None
    return cmp_sym


def _match_data(f: FNode) -> tuple[FNode, int] | None:
    """Match the ``a_i_e`` factor: either a bare symbol ``b`` or ``(+ k b)``.

    Returns ``(b, k_mod_p)``; ``k`` is ``0`` for a bare symbol, ``p-1`` for
    constr_5 (``a_0 - 1``).
    """
    p = ARGS().field_type.value
    if f.is_symbol():
        return f, 0
    if f.node_type() == operators.PLUS:
        terms = _flatten(operators.PLUS, f)
        const_total = 0
        sym = None
        for t in terms:
            c = _int_constant(t)
            if c is not None:
                const_total = (const_total + c) % p
                continue
            if sym is not None:
                return None
            if not t.is_symbol():
                return None
            sym = t
        if sym is None:
            return None
        return sym, const_total
    return None


def _match_inner_with_qvar(inner: FNode, qvar: FNode):
    """Match the inner expression ``(* X sign) + qvar`` of constr_5..8.

    Returns ``(data, data_offset, cmp)`` or ``None``. ``data`` is the limb
    symbol ``a_i``, ``data_offset`` is the constant added to it (``-1 mod p``
    only for ``i==0``), and ``cmp`` is the ``cmp_result`` symbol shared with
    the ``sign`` factor.
    """
    terms = _flatten(operators.PLUS, inner)
    if len(terms) != 2:
        return None
    qvar_seen = False
    other = None
    for t in terms:
        if t == qvar:
            if qvar_seen:
                return None
            qvar_seen = True
        else:
            if other is not None:
                return None
            other = t
    if not qvar_seen or other is None:
        return None
    coeff, factors = _split_product(other)
    if coeff != 1 or len(factors) != 2:
        return None
    for sign_f, data_f in (factors, list(reversed(factors))):
        cmp = _match_sign(sign_f)
        if cmp is None:
            continue
        data = _match_data(data_f)
        if data is None:
            continue
        b, off = data
        return b, off, cmp
    return None


def _match_constraint(node: FNode, qvar: FNode):
    """Match a single ``DiffMarkerConstraint`` (constr_5..constr_8) for ``qvar``.

    Two equivalent shapes are recognized:

    * Pre-rewrite (the canonical form emitted by the encoder)::

          (= (mod (* dm (+ (* X sign) qvar)) p) 0)

    * Post-rewrite (``simplify_rewrite`` splits the product into a disjunction
      because ``dm`` is boolean)::

          (or (= dm 0) (= (mod (+ (* X sign) qvar) p) 0))

    On match, returns ``{dm, data, data_offset, cmp}`` describing the pattern.
    """
    inner = _unwrap_zero_mod_eq(node)
    if inner is not None:
        coeff, factors = _split_product(inner)
        if coeff != 1 or len(factors) != 2:
            return None
        for dm_f, rest_f in (factors, list(reversed(factors))):
            if not (dm_f.is_symbol() and "diff_marker" in dm_f.symbol_name()):
                continue
            inside = _match_inner_with_qvar(rest_f, qvar)
            if inside is None:
                continue
            b, off, cmp = inside
            return {"dm": dm_f, "data": b, "data_offset": off, "cmp": cmp}
        return None

    if not node.is_or():
        return None
    args = list(node.args())
    if len(args) != 2:
        return None
    dm = None
    eq_node = None
    for a in args:
        if not a.is_equals():
            return None
        l, r = a.arg(0), a.arg(1)
        if _int_constant(l) == 0 and r.is_symbol() and "diff_marker" in r.symbol_name():
            if dm is not None:
                return None
            dm = r
            continue
        if _int_constant(r) == 0 and l.is_symbol() and "diff_marker" in l.symbol_name():
            if dm is not None:
                return None
            dm = l
            continue
        if eq_node is not None:
            return None
        eq_node = a
    if dm is None or eq_node is None:
        return None
    inner = _unwrap_zero_mod_eq(eq_node)
    if inner is None:
        return None
    inside = _match_inner_with_qvar(inner, qvar)
    if inside is None:
        return None
    b, off, cmp = inside
    return {"dm": dm, "data": b, "data_offset": off, "cmp": cmp}


def _diff_marker_index(sym: FNode) -> int | None:
    """Extract the limb index ``N`` from a ``...diff_marker__N...`` symbol name."""
    name = sym.symbol_name()
    i = name.find("diff_marker__")
    if i < 0:
        return None
    rest = name[i + len("diff_marker__"):]
    j = 0
    while j < len(rest) and rest[j].isdigit():
        j += 1
    if j == 0:
        return None
    return int(rest[:j])


def _build_skolem(matches: dict[int, dict], cmp: FNode, p: int) -> FNode:
    """Build the canonical ``diff_val`` witness as a nested ``Ite`` modulo ``p``.

    Mirrors OpenVM ``run_less_than`` against the constant ``c = (1, 0, 0, 0)``
    (LSB-first): scan limbs MSB-first and pick the first index where the
    operand differs from ``c``::

        if   b3 != 0: diff_val = (0 - b3) * sign     # -b3 * sign
        elif b2 != 0: diff_val = -b2 * sign
        elif b1 != 0: diff_val = -b1 * sign
        elif b0 != 1: diff_val = (1 - b0) * sign
        else        : diff_val = 0

    The expression is built bottom-up: the ``b0 != 1`` branch is wrapped
    inside the ``b1 != 0`` ``Ite``, and so on.
    ``-x`` is encoded as ``(p-1) * x`` to stay in the unsigned residue ring.
    """
    sign = wrap_mod(Plus(Int(p - 1), Times(Int(2), cmp)))

    def neg_x_sign(x: FNode) -> FNode:
        return wrap_mod(Times(Int(p - 1), x, sign))

    expr = Int(0)
    m = matches[0]
    expr = Ite(
        Equals(m["data"], Int(1)),
        expr,
        wrap_mod(Times(Plus(Int(1), Times(Int(p - 1), m["data"])), sign)),
    )
    for i in (1, 2, 3):
        m = matches[i]
        expr = Ite(Equals(m["data"], Int(0)), expr, neg_x_sign(m["data"]))
    return wrap_mod(expr)


def _build_marker_skolems(matches: dict[int, dict]) -> list[tuple[FNode, FNode]]:
    """Build canonical ``diff_marker__i`` witnesses against ``c = (1, 0, 0, 0)``.

    OpenVM sets ``marker[i] = 1`` exactly at the highest index where the operand
    differs from ``c`` (LSB-first ``c = (1, 0, 0, 0)``)::

        marker[3] = 1 iff b3 != 0
        marker[2] = 1 iff b3 = 0 ∧ b2 != 0
        marker[1] = 1 iff b3 = 0 ∧ b2 = 0 ∧ b1 != 0
        marker[0] = 1 iff b3 = 0 ∧ b2 = 0 ∧ b1 = 0 ∧ b0 != 1

    Returned as a list of ``(dm_var, skolem_expr)`` pairs (one per limb).
    Pinning these instead of the same-name ``before-dm_i = after-dm_i`` skolem
    avoids the soundness hole introduced by the optimizer's ``EqualZeroCheck``
    rewrite, which leaves the after-side markers unconstrained.
    """
    b0, b1, b2, b3 = (matches[i]["data"] for i in range(4))
    eq3 = Equals(b3, Int(0))
    eq2 = Equals(b2, Int(0))
    eq1 = Equals(b1, Int(0))
    eq0 = Equals(b0, Int(1))
    dm3_skolem = Ite(eq3, Int(0), Int(1))
    dm2_skolem = Ite(eq3, Ite(eq2, Int(0), Int(1)), Int(0))
    dm1_skolem = Ite(eq3, Ite(eq2, Ite(eq1, Int(0), Int(1)), Int(0)), Int(0))
    dm0_skolem = Ite(
        eq3, Ite(eq2, Ite(eq1, Ite(eq0, Int(0), Int(1)), Int(0)), Int(0)), Int(0)
    )
    return [
        (matches[0]["dm"], dm0_skolem),
        (matches[1]["dm"], dm1_skolem),
        (matches[2]["dm"], dm2_skolem),
        (matches[3]["dm"], dm3_skolem),
    ]


def _strip_prefix(name: str) -> str:
    """Strip the verifier's ``before-``/``after-`` symbol prefix, if present."""
    for prefix in ("before-", "after-"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def _find_and_build_witnesses(body: FNode, diff_val_vars):
    """Match ``DiffMarkerConstraint`` patterns for each ``diff_val`` variable
    and return ``(diff_val_var, matches, cmp_var)`` triples for successful matches.
    """
    results = []
    for dv in diff_val_vars:
        matches: dict[int, dict] = {}
        cmp_var = None
        for node in _iter_nodes(body):
            m = _match_constraint(node, dv)
            if m is None:
                continue
            idx = _diff_marker_index(m["dm"])
            if idx is None or idx not in (0, 1, 2, 3):
                continue
            expected_off = (ARGS().field_type.value - 1) % ARGS().field_type.value if idx == 0 else 0
            if m["data_offset"] != expected_off:
                continue
            if cmp_var is None:
                cmp_var = m["cmp"]
            elif cmp_var != m["cmp"]:
                continue
            if idx in matches:
                if matches[idx] != m:
                    continue
            else:
                matches[idx] = m
        if cmp_var is not None and set(matches.keys()) == {0, 1, 2, 3}:
            results.append((dv, matches, cmp_var))
    return results


def contribute(skolem_map, body: FNode) -> None:
    """Pin OpenVM ``EqualZeroCheck`` witnesses on ``skolem_map`` from ``body``.

    Walks the disjunctive forall body for every ``diff_val`` qvar of the
    map, and for each one that has all four ``DiffMarkerConstraint``
    shapes pins both the ``diff_val`` witness and the four
    ``diff_marker__i`` witnesses (when they are themselves qvars).
    Already-pinned qvars on ``skolem_map`` are left untouched.
    """
    targets = [
        v for v in skolem_map.qvars
        if _strip_prefix(v.symbol_name()).startswith("diff_val")
    ]
    if not targets:
        return

    p = ARGS().field_type.value
    for dv, matches, cmp_var in _find_and_build_witnesses(body, targets):
        skolem = _build_skolem(matches, cmp_var, p)
        skolem_map.pin(dv, skolem, source="rules")
        for dm_var, dm_skolem in _build_marker_skolems(matches):
            skolem_map.pin(dm_var, dm_skolem, source="rules")


def _swap_prefix(name: str) -> str | None:
    """Swap ``before-`` ↔ ``after-`` prefix. Returns ``None`` if neither."""
    if name.startswith("before-"):
        return "after-" + name[len("before-"):]
    if name.startswith("after-"):
        return "before-" + name[len("after-"):]
    return None


def contribute_free(smt_script, qvars: set[FNode]) -> list[tuple[FNode, FNode]]:
    """Pin free (non-quantified) ``diff_val`` and ``diff_marker`` variables.

    When the ``rule_based`` optimizer replaces the ``EqualZeroCheck``
    constraint set, the ``diff_val`` / ``diff_marker`` variables lose
    their defining constraints on the *after* side but remain referenced
    in bus interactions.  In the soundness encoding these variables are
    free (not quantified), so the solver can pick arbitrary values that
    trivially violate the *before* side.

    The constraints for these free variables do NOT exist in the SMT file
    (they were removed by the optimizer). Instead, this function:

    1. Finds free ``diff_val``/``diff_marker`` variables (non-quantified).
    2. Identifies the corresponding quantified counterpart with the
       opposite prefix (``before-`` ↔ ``after-``).
    3. Matches DiffMarkerConstraint patterns on the quantified counterpart
       (which still has its constraints in the forall body).
    4. Builds witness expressions for the free variables by swapping symbol
       prefixes in the quantified witness.
    """
    declared: dict[str, FNode] = {}
    for cmd in smt_script:
        if cmd.name == "declare-fun":
            sym = cmd.args[0]
            if sym.is_symbol():
                declared[sym.symbol_name()] = sym

    free_diff_vals = []
    for cmd in smt_script:
        if cmd.name == "declare-fun":
            sym = cmd.args[0]
            if not sym.is_symbol():
                continue
            stripped = _strip_prefix(sym.symbol_name())
            if stripped.startswith("diff_val") and sym not in qvars:
                free_diff_vals.append(sym)

    if not free_diff_vals:
        return []

    qvar_diff_vals = [v for v in qvars if _strip_prefix(v.symbol_name()).startswith("diff_val")]
    if not qvar_diff_vals:
        return []

    forall_body = None
    for cmd in smt_script:
        if cmd.name != "assert":
            continue
        for node in _iter_nodes(cmd.args[0]):
            if node.is_forall():
                forall_body = node.arg(0)
                break
        if forall_body is not None:
            break

    if forall_body is None:
        return []

    p = ARGS().field_type.value
    qvar_results = _find_and_build_witnesses(forall_body, qvar_diff_vals)

    stripped_to_qvar_match: dict[str, tuple] = {}
    for dv, matches, cmp_var in qvar_results:
        stripped = _strip_prefix(dv.symbol_name())
        stripped_to_qvar_match[stripped] = (matches, cmp_var)

    pins: list[tuple[FNode, FNode]] = []
    for free_dv in free_diff_vals:
        stripped = _strip_prefix(free_dv.symbol_name())
        entry = stripped_to_qvar_match.get(stripped)
        if entry is None:
            continue
        q_matches, q_cmp = entry

        def swap_sym(sym: FNode) -> FNode:
            swapped = _swap_prefix(sym.symbol_name())
            if swapped is None or swapped not in declared:
                return sym
            return declared[swapped]

        free_matches: dict[int, dict] = {}
        for idx, m in q_matches.items():
            free_matches[idx] = {
                "dm": swap_sym(m["dm"]),
                "data": swap_sym(m["data"]),
                "data_offset": m["data_offset"],
                "cmp": swap_sym(m["cmp"]),
            }

        free_cmp = swap_sym(q_cmp)
        skolem = _build_skolem(free_matches, free_cmp, p)
        pins.append((free_dv, skolem))
        for dm_var, dm_skolem in _build_marker_skolems(free_matches):
            if dm_var not in qvars:
                pins.append((dm_var, dm_skolem))

    if pins:
        logging.info(f"skolem rules-free: pinning {len(pins)} free diff_val/diff_marker variables")
    return pins
