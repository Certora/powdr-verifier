"""APC equivalence verification: encode completeness and soundness as SMT-LIB.

Loads before/after APC dumps, builds the cross-dump I/O relation, emits annotated
scripts for external solvers, and records outputs via ``Action`` telemetry objects.
"""
import copy
import logging
from pathlib import Path

from .encoding.utils import get_is_valid
from .report.action import Action
from .smt.encoding import collect_variables
from .smt.conversion import SmtConverter
from .smt.utils import *
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, load_json
from .verify.bug_injection import apply_injection
from .verify.memory_bus_alignment import BEFORE_PREFIX, AFTER_PREFIX, emit_memory_equalities
from .verify import SetInfos, SkolemPinKind
from .verify.skolem_pins import derived_columns_skolem_setinfo, drop_mirrored_derived


def encoding(before, after, qvars, io_relation, additional_asserts=[]):
    """Build the verification formula without any encoder-side model map.

    The forall body is the negation of (after.constraints AND
    ``io_relation``); the ``simplify_skolem`` pass
    later attaches per-qvar witnesses (rules / derived /
    same-name) as ``Not(q = expr)`` disjuncts which ``simplify_lift_forall``
    hoists out as top-level assertions.
    """
    res = And(
        *before.constraints,
        ForAll(
            qvars,
            Or(
                Not(And(*after.constraints)),
                Not(io_relation),
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

    if ARGS().inject is not None:
        old_before = copy.deepcopy(before)
        old_after = copy.deepcopy(after)
        apply_injection(before, after)
        assert before != old_before or after != old_after, "injection did not change the dumps"

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

        substitutions = {}
        if ARGS().substitutions is not None:
            substitutions = before_conv.convert_substitutions(load_json(ARGS().substitutions))

        io_relation, iorelvars = before_conv.bus_interaction_encoder.build_io_relation(
            after_conv.bus_interaction_encoder
        )
        var1 = collect_variables(before_smt) | iorelvars
        var2 = collect_variables(after_smt) | iorelvars
        globals = before_smt.globals | after_smt.globals
        auxiliaries = frozenset.union(
            frozenset(),
            *before_conv.bus_interaction_encoder.get_auxiliaries().values(),
            *after_conv.bus_interaction_encoder.get_auxiliaries().values(),
        )

        # Derived columns defined identically on both sides get no functional
        # pin; the skolem_names same-name fallback pins them instead (see
        # drop_mirrored_derived).
        after_derived_pins = drop_mirrored_derived(
            after_smt.derived, before_smt.derived, f"{AFTER_PREFIX}-", f"{BEFORE_PREFIX}-"
        )
        before_derived_pins = drop_mirrored_derived(
            before_smt.derived, after_smt.derived, f"{BEFORE_PREFIX}-", f"{AFTER_PREFIX}-"
        )
        derived_for_soundness = {**after_derived_pins, **before_derived_pins}

        def pin_metadata(
            formula: FNode,
            derived: dict,
            *,
            substitutions_map: dict | None = None,
            reverse: bool = False,
            smt_outfile: Path | None = None,
        ):
            info = SetInfos()
            if substitutions_map:
                info += derived_columns_skolem_setinfo(
                    formula, substitutions_map, kind=SkolemPinKind.SUBSTITUTION
                )
            info += derived_columns_skolem_setinfo(formula, derived, kind=SkolemPinKind.DERIVED)
            info += emit_memory_equalities(
                before,
                after,
                before_conv,
                after_conv,
                before_constraints=list(before_smt.derived.values())
                + list(substitutions.values()),
                after_constraints=list(after_smt.derived.values()),
                reverse=reverse,
                smt_dump_base=smt_outfile,
                parent_action=action,
            )
            return info

        if not ARGS().skip_completeness:
            outfile = ARGS().output.with_suffix(".completeness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; completeness check\n")
                completeness = encoding(
                    before_smt,
                    after_smt,
                    var2 - globals,
                    io_relation,
                )
                info = pin_metadata(completeness, after_derived_pins, reverse=True, smt_outfile=outfile)

                logging.info(f"dumping completeness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    completeness, status='unsat', pin_info=info
                )
                write_smtlib_script(smtlib, dump)
                action += ("outputs", outfile)

        is_valid_before = get_is_valid(var1, "before")
        is_valid_after = get_is_valid(var2, "after")

        if not ARGS().skip_soundness and is_valid_before is None and is_valid_after is not None:
            logging.warning("is_valid was introduced, perform special soundness check")
            outfile = ARGS().output.with_suffix(".soundness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; soundness check\n")
                soundness = encoding(
                    after_smt,
                    before_smt,
                    var1 - globals,
                    io_relation,
                    additional_asserts=[Equals(is_valid_after, Int(1))],
                )
                info = pin_metadata(
                    soundness,
                    derived_for_soundness,
                    substitutions_map=substitutions,
                    smt_outfile=outfile,
                )
                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', pin_info=info
                )
                write_smtlib_script(smtlib, dump)
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
                write_smtlib_script(smtlib, dump)
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
                write_smtlib_script(smtlib, dump)
                action += ("outputs", outfile)
        elif not ARGS().skip_soundness:
            outfile = ARGS().output.with_suffix(".soundness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; soundness check\n")
                soundness = encoding(
                    after_smt,
                    before_smt,
                    var1 - globals,
                    io_relation,
                )
                info = pin_metadata(
                    soundness,
                    derived_for_soundness,
                    substitutions_map=substitutions,
                    smt_outfile=outfile,
                )

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', pin_info=info
                )
                write_smtlib_script(smtlib, dump)
                action += ("outputs", outfile)
        action += {"result": "success"}

    return action
