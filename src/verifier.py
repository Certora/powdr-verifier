import json
import sympy


from .encoding.utils import get_is_valid
from .report.action import Action
from .rewriter.conversion import to_smt, to_sympy
from .rewriter import rewrite
from .simplify.skolem_derived import SETINFO_PREFIX as SETINFO_DERIVED_PREFIX
from .simplify.skolem_pclookup import SETINFO_PREFIX as SETINFO_PCLOOKUP_PREFIX
from .simplify.skolem_utils import emit_pin_setinfo
from .smt.encoding import build_input_output_relation, collect_variables
from .smt.conversion import FormulaWithAxioms, SmtConverter
from .smt.utils import *
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, load_json

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"
#: Prefix for set-info annotations carrying shared bus array equalities.
#: Written by :func:`_shared_bus_arrays`, read by
#: :func:`.simplify.array_subst.simplify_array_subst`.
SETINFO_SHARED_ARRAYS_PREFIX = ":shared-array-"


def _memory_bus_id(data: dict) -> int | None:
    """Return the numeric bus ID for ``Memory``, or ``None`` if absent."""
    bus_ids = data.get("bus_map", {}).get("bus_ids", {})
    for bid, btype in bus_ids.items():
        if btype == "Memory":
            return int(bid)
    return None


def _shared_bus_arrays(
    before_data: dict, after_data: dict,
    before_conv: SmtConverter, after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    """Identify memory bus array symbols that are provably equal across sides.

    The memory bus is encoded as a chain of array variables
    (``memory-0-mult``, ``memory-1-mult``, ..., ``memory-N-mult`` for
    each field), where each step applies a ``Store`` driven by one bus
    interaction.  Both the *before* and *after* converters produce their
    own chain independently, even when many interactions are unchanged
    by the optimization step.

    This function compares the *raw* bus interactions (the JSON
    expressions before SMT conversion) element-by-element.  Because
    both sides use the same variable names (``before-``/``after-``
    prefixes are only added during ``convert_manual``), two raw
    interactions that are equal as JSON values are guaranteed to
    represent the same memory access.

    If the first ``k`` interactions are identical, then the array state
    at steps 0 through ``k`` is the same on both sides — they start
    from equal base arrays (equated by ``build_input_output_relation``)
    and apply the same sequence of stores.  Similarly, if the last ``m``
    interactions match, the array state converges from the end.

    For each such shared step, every array-typed auxiliary symbol
    (``memory-{step}-mult``, ``memory-{step}-data0``, etc.) is paired
    with its counterpart on the other side.  The resulting map
    ``{before_sym: after_sym}`` is emitted as ``set-info`` annotations
    that the ``array_subst`` simplifier pass later reads and converts
    into ``(assert (= before-X after-X))`` assertions.

    Why only array-typed symbols?
        The intermediate non-array symbols (``-1``, ``-2``, ``-new``
        suffixed ``Int`` variables from ``update_multidim_array``)
        were tested but asserting their equality actually hurts solver
        performance — Z3 handles array equalities far more efficiently
        via its specialized congruence closure than it handles large
        numbers of ``Int`` equality assertions.

    Returns
    -------
    dict[FNode, FNode]
        Map from before-side array symbols to their after-side
        counterparts.  Empty if no interactions match.
    """
    mem_id = _memory_bus_id(before_data)
    if mem_id is None:
        return {}

    # Extract raw memory bus interactions from the JSON (before SMT conversion).
    before_mem = [
        bi for bi in before_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]
    after_mem = [
        bi for bi in after_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]

    n = len(before_mem)
    if n != len(after_mem) or n == 0:
        return {}

    # Compare raw JSON directly — identical dicts mean identical interactions.
    # No prefix stripping needed because variable names are unprefixed in the
    # raw APC dump; the before-/after- prefixes are only added by SmtConverter.
    prefix_same = 0
    for i in range(n):
        if before_mem[i] != after_mem[i]:
            break
        prefix_same += 1

    suffix_same = 0
    for i in range(1, n + 1):
        if n - i < prefix_same:
            break
        if before_mem[-i] != after_mem[-i]:
            break
        suffix_same += 1

    # Build the set of array-chain step indices whose state is shared.
    # If interactions 0..k-1 are identical, steps 0..k are shared
    # (step 0 is the initial state, step k is the state after k stores).
    # Similarly from the suffix end.
    shared_steps: set[int] = set()
    for i in range(prefix_same + 1):
        shared_steps.add(i)
    for i in range(n - suffix_same, n + 1):
        shared_steps.add(i)

    if not shared_steps:
        return {}

    # Now use the encoder's auxiliary symbols to build the equality map.
    before_enc = before_conv.bus_interaction_encoder.memory
    after_enc = after_conv.bus_interaction_encoder.memory

    def strip_prefix(name: str) -> str:
        for p in (BEFORE_PREFIX + "-", AFTER_PREFIX + "-"):
            if name.startswith(p):
                return name[len(p):]
        return name

    ba = before_enc.auxiliaries if hasattr(before_enc, 'auxiliaries') else set()
    aa = after_enc.auxiliaries if hasattr(after_enc, 'auxiliaries') else set()

    # Index before-side array auxiliaries by their unprefixed name.
    before_by_suffix: dict[str, FNode] = {}
    for s in ba:
        if s.get_type().is_array_type():
            before_by_suffix[strip_prefix(s.symbol_name())] = s

    # Match each after-side array auxiliary to its before-side partner
    # if the step index falls within the shared range.
    subs: dict[FNode, FNode] = {}
    for s in aa:
        if not s.get_type().is_array_type():
            continue
        suffix = strip_prefix(s.symbol_name())
        partner = before_by_suffix.get(suffix)
        if partner is None or partner.get_type() != s.get_type():
            continue
        # Extract the step index from the name (e.g. "memory-5-mult" → 5).
        parts = suffix.split("-")
        if len(parts) >= 2:
            try:
                step = int(parts[1])
            except ValueError:
                continue
            if step in shared_steps:
                subs[partner] = s

    if subs:
        logging.warning(
            f"shared bus arrays: {len(subs)} symbols "
            f"(prefix={prefix_same}, suffix={suffix_same}, total={n})"
        )
    return subs


def _eq_pin_setinfo(prefix: str, pins: list[FNode]) -> list:
    """Wrap each pin equation as a ``set-info :{prefix}N`` command.

    Pins are kept as ``Equals(var, expr)`` ``FNode`` instances; the
    simplifier-side parser splits them into qvar and witness.
    """
    return [emit_pin_setinfo(prefix, i, eq) for i, eq in enumerate(pins)]


def _vars_only(symbols: frozenset[FNode]) -> frozenset[FNode]:
    """Drop UF function-typed symbols, keep plain variables.

    Used by the ``live`` filter on emitted pins: UFs (``uf_mod_inv``,
    ``pc_a``, etc.) are constant globals known to every encoding even
    when they happen to be unused in the actual constraints, so we
    don't want a derived equation to be filtered out merely because it
    mentions a UF the formula didn't reach. Whatever UFs the pins do
    reference are collected separately by :func:`_pin_ufs` and emitted
    as ``declare-fun``s alongside the set-info commands.
    """
    return frozenset(
        s for s in symbols if not s.symbol_type().is_function_type()
    )


def _pin_ufs(pins: list[FNode]) -> list[FNode]:
    """Return the UF function symbols referenced by ``pins``."""
    ufs: set[FNode] = set()
    for eq in pins:
        for s in eq.get_free_variables():
            if s.symbol_type().is_function_type():
                ufs.add(s)
    return sorted(ufs, key=lambda s: s.symbol_name())


def _derived_pins(
    derived: dict[FNode, FNode], live: frozenset[FNode]
) -> list[FNode]:
    """Return the equations from a ``derived`` / ``eliminations`` dict.

    Both ``after_smt.derived`` (derived columns) and
    ``before_conv.convert_eliminations(...)`` already canonicalize their
    values as ``Equals(var, expr)``. We only emit equations all of whose
    *variable* free symbols appear in ``live``: anything else references
    a variable the encoder has already eliminated and whose
    ``declare-fun`` will not be in the SMT script the simplifier reads
    back, so the round-trip parse would fail. UF function symbols are
    excluded from this check (see :func:`_vars_only`).
    """
    var_live = _vars_only(live)
    out: list[FNode] = []
    for eq in derived.values():
        if _vars_only(eq.get_free_variables()) <= var_live:
            out.append(eq)
    return out


def _pclookup_pins(
    conv: SmtConverter, known: dict[FNode, FNode], live: frozenset[FNode]
) -> list[FNode]:
    """Resolve pc-lookup pins for any pc whose value is known to be constant.

    ``known`` is the union of derived/elimination pins (``var -> expr``);
    we read constant pins for ``pc`` symbols, look up the corresponding
    instruction, and use ``find_unique_solution`` against the encoder's
    incremental ``constraint_solver`` (which already has the bus axioms
    and flag constraints accumulated as the encoding was built) to derive
    operand pins. Each resolved pin is returned as ``Equals(var, value)``.

    This is the ``ModelMapBuilder.__heuristic_pclookup`` logic, lifted
    out of the builder and made dump-only so we can serialize the
    result as ``set-info`` for the simplifier. The work has to happen
    here (not in the simplifier) because the same incremental solver
    state isn't reproducible from the post-NNF formula.
    """
    if conv.bus_interaction_encoder is None or not hasattr(
        conv.bus_interaction_encoder, "pc_lookup"
    ):
        return []
    encoder = conv.bus_interaction_encoder.pc_lookup

    pc_const: dict[FNode, int] = {}
    for var, expr in known.items():
        if not expr.is_equals():
            continue
        l, r = expr.arg(0), expr.arg(1)
        rhs = r if l == var else (l if r == var else None)
        if rhs is not None and rhs.is_int_constant():
            pc_const[var] = rhs.constant_value()

    out: list[FNode] = []
    for mult, (spc, sop, *rest) in encoder._interactions:
        if spc not in pc_const:
            continue
        op, *_ = encoder._get_instruction(pc_const[spc])
        res = find_unique_solution(conv.constraint_solver, Equals(sop, Int(op)))
        if res is None:
            continue
        for v, c in res.items():
            if v not in live:
                continue
            val = Int(c) if isinstance(c, int) else c
            if not val.get_free_variables() <= live:
                continue
            out.append(Equals(v, val))
    return out


def _skolem_setinfo(
    formula: FNode, conv: SmtConverter, derived: dict[FNode, FNode]
) -> tuple[list, list[FNode]]:
    """Produce the set-info commands and required UF declarations.

    Returns ``(setinfo_cmds, extra_decls)``: ``setinfo_cmds`` carries
    the ``derived`` / ``elimination`` equations and resolved pc-lookup
    pins for the simplifier-side skolem orchestrator
    (:mod:`.simplify.skolem`); ``extra_decls`` lists the UF function
    symbols referenced by those pins so :func:`convert_to_smt_script`
    can emit ``declare-fun``s for them even when no constraint of the
    formula happens to reach them (e.g. ``uf_mod_inv`` for derived
    columns of the form ``v = ite(d=0, 0, 1*uf_mod_inv(d))``).

    Pin equations whose *variable* free symbols are not free in
    ``formula`` are still filtered out: those variables will not be
    declared in the smt2 file and the parser would fail to resolve
    them back.
    """
    live = _collect_all_symbols(formula)
    derived_pins = _derived_pins(derived, live)
    pclookup_pins = _pclookup_pins(conv, derived, live)
    cmds = (
        _eq_pin_setinfo(SETINFO_DERIVED_PREFIX[1:], derived_pins)
        + _eq_pin_setinfo(SETINFO_PCLOOKUP_PREFIX[1:], pclookup_pins)
    )
    extra_decls = _pin_ufs(derived_pins + pclookup_pins)
    return cmds, extra_decls


def _collect_all_symbols(formula: FNode) -> frozenset[FNode]:
    """Return every symbol that occurs in ``formula`` (free or bound).

    ``FNode.get_free_variables`` excludes quantifier-bound vars; pins
    may reference vars that only appear as forall qvars, so we walk
    explicitly.
    """
    out: set[FNode] = set()

    def visit(n: FNode):
        if n.is_symbol():
            out.add(n)
        if n.is_quantifier():
            for q in n.quantifier_vars():
                if q.is_symbol():
                    out.add(q)
        for a in n.args():
            visit(a)

    visit(formula)
    return frozenset(out)


def encoding(before, after, qvars, input_relation, output_relation, additional_asserts=[]):
    """Build the verification formula without any encoder-side model map.

    The forall body is the negation of (after.constraints AND
    input_relation AND output_relation); the ``simplify_skolem`` pass
    later attaches per-qvar witnesses (rules / derived / pclookup /
    same-name) as ``Not(q = expr)`` disjuncts which ``simplify_lift_forall``
    hoists out as top-level assertions.
    """
    res = And(
        *before.constraints,
        ForAll(
            qvars,
            Or(
                Not(And(*after.constraints)),
                Not(input_relation),
                Not(output_relation),
            ),
        ),
        *before.axioms,
        *after.axioms,
        *additional_asserts,
    )
    if ARGS().elim_with_model:
        model = load_json(ARGS().elim_with_model)
        subs = {}
        for name, value in model.items():
            if isinstance(value, bool):
                subs[Symbol(name, BOOL)] = Bool(value)
            elif isinstance(value, int):
                subs[Symbol(name, INT)] = Int(value)
        res = res.substitute(subs)
    return res

def verify():
    """Verify our versions of equivalence."""

    before = load_apc_dump(ARGS().input_before)
    after = load_apc_dump(ARGS().input_after)

    block = BasicBlock(before["block"])
    assert block == BasicBlock(after["block"]), "The basic block has changed"

    with (
        Action("verify-encode") as action,
        SmtConverter(BEFORE_PREFIX, block) as before_conv,
        SmtConverter(AFTER_PREFIX, block) as after_conv,
    ):
        action += {"outputs": []}
        before_smt = before_conv.to_formula_with_axioms(before)
        after_smt = after_conv.to_formula_with_axioms(after)

        eliminations = {}
        if ARGS().eliminations is not None:
            eliminations = before_conv.convert_eliminations(load_json(ARGS().eliminations))


        # obtain input and output info
        inputs1 = before_conv.bus_interaction_encoder.get_inputs()
        inputs2 = after_conv.bus_interaction_encoder.get_inputs()
        outputs1 = before_conv.bus_interaction_encoder.get_outputs()
        outputs2 = after_conv.bus_interaction_encoder.get_outputs()
        input_relation = build_input_output_relation("INPUT RELATION", inputs1, inputs2)
        output_relation = build_input_output_relation(
            "OUTPUT RELATION", outputs1, outputs2
        )
        # Identify memory bus arrays that are identical on both sides
        # because the corresponding interactions didn't change.  The map
        # is emitted as set-info annotations and picked up by array_subst.
        shared_array_subs = _shared_bus_arrays(before, after, before_conv, after_conv)

        # obtain variables and globals
        var1 = collect_variables(before_smt)
        var2 = collect_variables(after_smt)
        globals = before_smt.globals | after_smt.globals
        auxiliaries = frozenset.union(frozenset(), *(
            before_conv.bus_interaction_encoder.get_auxiliaries()
            | after_conv.bus_interaction_encoder.get_auxiliaries()
        ).values())

        outfile = ARGS().output.with_suffix(".completeness.smt2")
        with open(outfile, "w") as dump:
            dump.write(";; completeness check\n")
            completeness = encoding(
                before_smt, after_smt, var2 - globals, input_relation, output_relation
            )
            extra, extra_decls = _skolem_setinfo(completeness, after_conv, after_smt.derived)
            # For completeness, after-vars are quantified, so the pins
            # go from after → before (the quantified side → the free side).
            extra += _eq_pin_setinfo(
                SETINFO_SHARED_ARRAYS_PREFIX[1:],
                [Equals(v, k) for k, v in shared_array_subs.items()],
            )

            logging.info(f"dumping completeness check to {dump.name}")
            smtlib = convert_to_smt_script(
                completeness, status='unsat', extra_setinfo=extra, extra_decls=extra_decls
            )
            pretty_print_smtlib(smtlib, dump)
            action += ("outputs", outfile)
        
        is_valid_before = get_is_valid(var1, "before")
        is_valid_after = get_is_valid(var2, "after")

        if is_valid_before is None and is_valid_after is not None:
            logging.warning("is_valid was introduced, perform special soundness check")
            outfile = ARGS().output.with_suffix(".soundness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; soundness check\n")
                soundness = encoding(
                    after_smt,
                    before_smt,
                    var1 - globals,
                    input_relation,
                    output_relation,
                    additional_asserts=[Equals(is_valid_after, Int(1))],
                )
                extra, extra_decls = _skolem_setinfo(soundness, before_conv, eliminations)
                # For soundness, before-vars are quantified, so the pins
                # go from before → after (the quantified side → the free side).
                extra += _eq_pin_setinfo(
                    SETINFO_SHARED_ARRAYS_PREFIX[1:],
                    [Equals(k, v) for k, v in shared_array_subs.items()],
                )

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', extra_setinfo=extra, extra_decls=extra_decls
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)

            outfile = ARGS().output.with_suffix(".soundness.zero-is-model.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; check that all zero is a model\n")
                logging.info(f"dumping zero is model check to {dump.name}")
                intvars = [ v for v in (var2 - auxiliaries) if v.get_type() == INT ]
                intvars = sorted(intvars, key=lambda x: x.symbol_name())
                smtlib = convert_to_smt_script(
                    And(
                        *after_smt.constraints,
                        *after_smt.axioms,
                        with_comment(
                            And(*[ Equals(v, Int(0)) for v in intvars ]),
                            "ZERO MODEL"
                        )
                    ),
                    status='sat'
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)

            outfile = ARGS().output.with_suffix(".soundness.invalid-all-mult-zero.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; check that all is_valid zero makes all multiplicities zero\n")
                logging.info(f"dumping invalid makes all multiplicities zero check to {dump.name}")

                multiplicities = []
                for encoder in after_conv.bus_interaction_encoder.encoders:
                    for interaction in encoder._interactions:
                        multiplicities.append(interaction.mult)
                smtlib = convert_to_smt_script(
                    And(
                        Equals(is_valid_after, Int(0)),
                        *after_smt.constraints,
                        Or(*[Not(Equals(mult, Int(0))) for mult in multiplicities ])
                    ),
                    status='unsat'
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)
        else:
            outfile = ARGS().output.with_suffix(".soundness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; soundness check\n")
                soundness = encoding(
                    after_smt, before_smt, var1 - globals, input_relation, output_relation
                )
                extra, extra_decls = _skolem_setinfo(soundness, before_conv, eliminations)
                # For soundness, before-vars are quantified, so the pins
                # go from before → after (the quantified side → the free side).
                extra += _eq_pin_setinfo(
                    SETINFO_SHARED_ARRAYS_PREFIX[1:],
                    [Equals(k, v) for k, v in shared_array_subs.items()],
                )

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', extra_setinfo=extra, extra_decls=extra_decls
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)
        action += {"result": "success"}

    return action
