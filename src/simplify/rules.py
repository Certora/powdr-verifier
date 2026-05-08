"""Skolemization pass for OpenVM-style ``EqualZeroCheck`` patterns.

Background
----------
The powdr ``rule_based`` optimizer (see
``powdr/constraint-solver/src/rule_based_optimizer/rules.rs``) recognizes the
constraint set produced by OpenVM's ``LessThan`` core (see
https://github.com/powdr-labs/openvm/blob/4300c42df8f860085b6ca46311f2750a01da3dec/extensions/rv32im/circuit/src/less_than/core.rs)
and replaces it with a much simpler equivalent using a fresh ``inv_of_sum``
witness. The original constraint set has the shape (per limb ``i in 0..4``)::

    diff_marker__i * (a_i_e * sign + diff_val) = 0           (constr_5..8)
    (1 - sum_dm_>=i) * (-a_i) * sign         = 0             (constr_0..2)
    (1 - sum_dm)     * (1 - a_0) * sign      = 0             (constr_4)
    (1 - sum_dm)     * cmp_result            = 0             (constr_3)
    sum_dm * (sum_dm - 1)                    = 0             (constr_9)
    diff_marker__i * (diff_marker__i - 1)    = 0
    sign = 2 * cmp_result - 1

where ``a_0_e == a_0 - 1`` (i.e. ``c[0] = 1``) and ``a_i_e == a_i`` for
``i in {1,2,3}`` (i.e. ``c[i] = 0``). In other words the constraints encode a
4-limb less-than against the constant ``c = (1, 0, 0, 0)`` (LSB-first).

The verifier soundness check turns the *before* (pre-optimization) constraint
system into a universal: ``forall <before-vars>. Implies(map, Or(Not(C_i)))``.
Most ``before-`` variables are pinned to their ``after-`` counterpart through
the ``ModelMapBuilder`` same-name heuristic and are then lifted out of the
forall by ``simplify_lift_forall``. The ``EqualZeroCheck`` rewrite drops every
constraint that connects ``diff_val`` and ``diff_marker__i`` to ``b`` in the
*after* system, so:

* ``before-diff_val`` has no ``after-`` counterpart at all and stays
  universally quantified. With ``diff_val`` free, ``Not(before.constraints)``
  is trivially satisfiable for any inconsistent ``diff_val``.
* ``before-diff_marker__i`` does have an ``after-diff_marker__i`` of the same
  name, but the after-side variable is unconstrained. The same-name map
  therefore propagates an arbitrary ``after-dm`` choice (typically ``0``)
  onto ``before-dm``, blocking the only consistent witness in which exactly
  one marker is one.

Either alone is enough to make the soundness check spuriously satisfiable; in
practice both are needed.

What this pass does
-------------------
For every ``forall`` whose body is a disjunction (NNF) and that quantifies a
variable whose stripped name starts with ``diff_val``, this pass:

1. Locates the four ``DiffMarkerConstraint`` shapes for that ``diff_val`` in
   the body (matched in both pre-rewrite ``(= (mod (* dm (+ (* X sign) dv)) p) 0)``
   and post-rewrite ``(or (= dm 0) (= (mod (+ (* X sign) dv) p) 0))`` forms),
   indexed by the trailing number of the ``diff_marker__N`` symbol.
2. Confirms a single shared ``cmp_result``, requires the constr_5 entry to
   carry the ``a_0 - 1`` offset, and requires constr_6..8 to carry no offset.
3. Builds the canonical OpenVM witness for ``diff_val``: scan limbs MSB-first
   and pick the first differing limb against ``c = (1, 0, 0, 0)``::

       diff_val := (c[i] - b[i]) * sign   for the highest i with b[i] != c[i]
                 := 0                     when b == c

   Encoded as nested ``Ite`` (modulo ``p``).
4. Builds the canonical OpenVM witness for each ``diff_marker__i``: ``1`` at
   the highest index where ``b[i] != c[i]``, ``0`` everywhere else. Also
   nested ``Ite``.
5. Appends ``Not(diff_val = skolem)`` and ``Not(dm_i = skolem_i)`` (only when
   ``dm_i`` is actually quantified by this forall) as fresh disjuncts.

The downstream ``simplify_lift_forall`` pass recognises these disjuncts (the
qvar is on one side of an equality and the other side mentions no qvar) and
hoists ``qvar = skolem`` out as a top-level assertion, removing ``qvar`` from
the universal. From the solver's perspective this is the standard
``forall x. (x != t) | P(x)  ==  P(t)`` rewrite: it does not weaken the
formula, it only commits each variable to the witness OpenVM would actually
produce, so the remaining body becomes a concrete (per ``b``, ``cmp_result``)
constraint instead of a universal. For ``diff_marker``, lifting also turns
the still-present same-name map disjunct ``Not(before-dm = after-dm)`` into a
real constraint linking ``after-dm`` to the canonical witness, which is what
recovers soundness when the optimizer's ``EqualZeroCheck`` rewrite drops the
original marker constraints.

This pass therefore must run after ``nnf`` (so the body is an ``Or``) and
before ``lift``.
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
    Pinning these alongside ``diff_val`` lets ``simplify_lift_forall`` discard
    the bogus same-name map equalities ``before-dm_i = after-dm_i`` (which the
    optimizer's ``EqualZeroCheck`` rewrite leaves unconstrained on the after
    side) and force the canonical OpenVM witness instead.
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


def _peel_mod(f: FNode) -> FNode:
    """Strip an outer ``(mod x p)`` (with ``p`` the field prime) and return ``x``."""
    if f.node_type() != operators.MOD:
        return f
    if _int_constant(f.arg(1)) != ARGS().field_type.value:
        return f
    return f.arg(0)


def _is_same_name_map_disjunct(d: FNode, qvars: frozenset[FNode]) -> bool:
    """Return ``True`` for a body disjunct ``Not(before-X = after-X)`` whose ``before-X`` symbol is in ``qvars``.

    These disjuncts are emitted by ``ModelMapBuilder``'s same-name heuristic
    via the ``map`` conjunction at encoding time; after ``nnf`` they appear as
    ``Not(eq)`` disjuncts of the forall body, with the ``after`` side wrapped
    in ``(mod _ p)`` because the encoder emits all field equalities through
    ``wrap_mod``. ``simplify_lift_forall`` is happy to lift either this map
    equality or our skolem equality but only one per qvar, and Python ``set``
    iteration order is not stable. To guarantee that the canonical witness
    wins, we drop the same-name map disjuncts for the qvars we are about to
    skolemize.
    """
    if not qvars:
        return False
    if not d.is_not():
        return False
    eq = d.arg(0)
    if not eq.is_equals():
        return False
    l, r = _peel_mod(eq.arg(0)), _peel_mod(eq.arg(1))
    if not (l.is_symbol() and r.is_symbol()):
        return False
    for vside, other in ((l, r), (r, l)):
        if vside not in qvars:
            continue
        if _strip_prefix(vside.symbol_name()) == _strip_prefix(other.symbol_name()):
            return True
    return False


class _RulesWalker(IdentityDagWalker):
    """Visit each ``forall`` and inject a skolem disjunct for matching qvars."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.applied_diff_val = 0
        self.applied_diff_marker = 0

    def walk_forall(self, formula, args, **kwargs):
        body = args[0]
        if not body.is_or():
            return formula
        qvars = list(formula.quantifier_vars())
        qvar_set = frozenset(qvars)
        targets = [v for v in qvars if _strip_prefix(v.symbol_name()).startswith("diff_val")]
        if not targets:
            return formula

        new_disjuncts = []
        suppressed_qvars: set[FNode] = set()
        for qvar in targets:
            matches: dict[int, dict] = {}
            cmp_var = None
            for node in _iter_nodes(body):
                m = _match_constraint(node, qvar)
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
            if cmp_var is None or set(matches.keys()) != {0, 1, 2, 3}:
                continue
            skolem = _build_skolem(matches, cmp_var, ARGS().field_type.value)
            new_disjuncts.append(Not(Equals(qvar, skolem)))
            self.applied_diff_val += 1
            for dm_var, dm_skolem in _build_marker_skolems(matches):
                if dm_var in qvar_set:
                    new_disjuncts.append(Not(Equals(dm_var, dm_skolem)))
                    suppressed_qvars.add(dm_var)
                    self.applied_diff_marker += 1

        if not new_disjuncts:
            return formula
        kept = [d for d in body.args() if not _is_same_name_map_disjunct(d, suppressed_qvars)]
        return ForAll(qvars, Or(*kept, *new_disjuncts))


def simplify_rules(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Add OpenVM ``LessThan`` ``diff_val`` skolem definitions to forall bodies.

    See the module docstring for the full reasoning. The pass is a no-op on
    forall nodes whose body is not a disjunction (run after ``nnf``) or that
    do not quantify a ``diff_val`` variable, and on ``diff_val`` quantifiers
    where the four ``DiffMarkerConstraint`` shapes cannot all be located.
    """
    w = _RulesWalker(env=get_env())
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])
    if w.applied_diff_val or w.applied_diff_marker:
        logging.info(
            f"rules: applied skolem for {w.applied_diff_val} diff_val and "
            f"{w.applied_diff_marker} diff_marker variable(s)"
        )
    return smt_script
