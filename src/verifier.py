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

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', extra_setinfo=extra, extra_decls=extra_decls
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)
        action += {"result": "success"}

    return action
