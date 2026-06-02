"""APC equivalence verification: encode completeness and soundness as SMT-LIB.

Loads before/after APC dumps, builds input/output relations and shared-bus
array metadata, emits annotated scripts for external solvers, and records
outputs via ``Action`` telemetry objects.
"""
import logging
from pathlib import Path

from .encoding.utils import get_is_valid
from .report.action import Action
from .smt.encoding import collect_variables
from .smt.conversion import SmtConverter
from .smt.utils import *
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, load_json
from .verify.memory_bus_alignment import BEFORE_PREFIX, AFTER_PREFIX, emit_memory_equalities
from .verify.skolem_pins import derived_columns_skolem_setinfo


def encoding(before, after, qvars, input_relation, output_relation, additional_asserts=[]):
    """Build the verification formula without any encoder-side model map.

    The forall body is the negation of (after.constraints AND
    input_relation AND output_relation); the ``simplify_skolem`` pass
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

        input_relation = before_conv.bus_interaction_encoder.build_io_relation(
            after_conv.bus_interaction_encoder, "input"
        )
        output_relation = before_conv.bus_interaction_encoder.build_io_relation(
            after_conv.bus_interaction_encoder, "output"
        )
        var1 = collect_variables(before_smt)
        var2 = collect_variables(after_smt)
        globals = before_smt.globals | after_smt.globals
        auxiliaries = frozenset.union(
            frozenset(),
            *before_conv.bus_interaction_encoder.get_auxiliaries().values(),
            *after_conv.bus_interaction_encoder.get_auxiliaries().values(),
        )

        map_sources = {**eliminations, **after_smt.derived, **before_smt.derived}

        def pin_metadata(
            formula: FNode,
            derived: dict,
            *,
            reverse: bool = False,
            smt_outfile: Path | None = None,
        ):
            info = derived_columns_skolem_setinfo(formula, derived)
            info += emit_memory_equalities(
                before,
                after,
                before_conv,
                after_conv,
                before_constraints=before_smt.constraints,
                after_constraints=after_smt.constraints,
                reverse=reverse,
                smt_dump_base=smt_outfile,
            )
            return info

        outfile = ARGS().output.with_suffix(".completeness.smt2")
        with open(outfile, "w") as dump:
            dump.write(";; completeness check\n")
            completeness = encoding(
                before_smt,
                after_smt,
                var2 - globals,
                input_relation,
                output_relation,
            )
            info = pin_metadata(completeness, after_smt.derived, reverse=True, smt_outfile=outfile)

            logging.info(f"dumping completeness check to {dump.name}")
            smtlib = convert_to_smt_script(
                completeness, status='unsat', pin_info=info
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
                info = pin_metadata(soundness, map_sources, smt_outfile=outfile)
                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', pin_info=info
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
                    after_smt,
                    before_smt,
                    var1 - globals,
                    input_relation,
                    output_relation,
                )
                info = pin_metadata(soundness, map_sources, smt_outfile=outfile)

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(
                    soundness, status='unsat', pin_info=info
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)
        action += {"result": "success"}

    return action
