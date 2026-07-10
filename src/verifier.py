"""APC equivalence verification: encode completeness and soundness as SMT-LIB.

Loads before/after APC dumps, builds the cross-dump I/O relation, emits annotated
scripts for external solvers, and records outputs via ``Action`` telemetry objects.
"""
import copy
import logging
from pathlib import Path

from .encoding.utils import get_is_valid
from .report.action import Action
from .smt.conversion import SmtConverter
from .smt.utils import *
from .smt_backends.pysmt import disable_typecheck
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, open_file, SMT_ENCODING, load_json
from .utils.stats import init_stats_run, set_stats_tag, stats_enabled
from .verify.bug_injection import apply_injection
from .verify.preanalysis import analyze_memory_bus_alignment, apply_skip_trivial
from .verify.memory_bus_alignment import BEFORE_PREFIX, AFTER_PREFIX, emit_memory_equalities
from .verify import SetInfos, SkolemPinKind
from .verify.skolem_pins import derived_columns_skolem_setinfo, drop_mirrored_derived


def _filter_mirrored_constraints(before, after):
    """Return ``after`` with constraints removed that mirror ``before.constraints``."""
    before_canon = {
        strip_prefix_from_vars(c, f"{BEFORE_PREFIX}-") for c in before.constraints
    }
    kept: list[FNode] = []
    dropped = 0
    for c in after.constraints:
        if strip_prefix_from_vars(c, f"{AFTER_PREFIX}-") in before_canon:
            dropped += 1
            logging.debug("filter-constraints: dropped mirrored constraint: %s", c)
            continue
        kept.append(c)
    if dropped:
        logging.info("filter-constraints: dropped %d mirrored constraint(s)", dropped)
        return after._replace(constraints=kept)
    return after


def encoding(before, after, qvars, io_relation, additional_asserts=[]):
    """Build the verification formula without any encoder-side model map.

    The forall body is the negation of (after.constraints AND
    ``io_relation``); the ``simplify_skolem`` pass
    later attaches per-qvar witnesses (rules / derived /
    same-name) as ``Not(q = expr)`` disjuncts which ``simplify_lift_forall``
    hoists out as top-level assertions.
    """
    if ARGS().filter_constraints:
        after = _filter_mirrored_constraints(before, after)
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

    if stats_enabled():
        init_stats_run(wipe=True)
        set_stats_tag("encode")

    with Action("encode") as action:
        action += {"outputs": []}

        # Encoding builds well-typed formulas programmatically; saves ~30% encode on 2099828 step 0.
        disable_typecheck()

        before = load_apc_dump(ARGS().input_before)
        after = load_apc_dump(ARGS().input_after)

        apply_skip_trivial(before, after)
        with action.action("membus"):
            memory_bus_alignment = analyze_memory_bus_alignment(before, after)

        if ARGS().inject is not None:
            old_before = copy.deepcopy(before)
            old_after = copy.deepcopy(after)
            apply_injection(before, after)
            assert before != old_before or after != old_after, "injection did not change the dumps"

        block = BasicBlock(before["block"])
        assert block == BasicBlock(after["block"]), "The basic block has changed"

        optimization_step = ARGS().optimization_step
        if optimization_step:
            action += {"optimization_step": optimization_step}

        with (
            SmtConverter(
                BEFORE_PREFIX, block,
                memory_bus_alignment=memory_bus_alignment,
                source_path=ARGS().input_before,
            ) as before_conv,
            SmtConverter(
                AFTER_PREFIX, block,
                memory_bus_alignment=memory_bus_alignment,
                source_path=ARGS().input_after,
            ) as after_conv,
        ):
            before_smt = before_conv.to_formula_with_axioms(before)
            after_smt = after_conv.to_formula_with_axioms(after)

            substitutions = {}
            if ARGS().substitutions is not None:
                substitutions = before_conv.convert_substitutions(load_json(ARGS().substitutions))

            io_relation, iorelvars = before_conv.bus_interaction_encoder.build_io_relation(
                after_conv.bus_interaction_encoder
            )
            var1 = before_conv.symbols | iorelvars
            var2 = after_conv.symbols | iorelvars
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
                        substitutions_map, kind=SkolemPinKind.SUBSTITUTION
                    )
                info += derived_columns_skolem_setinfo(derived, kind=SkolemPinKind.DERIVED)
                info += emit_memory_equalities(
                    memory_bus_alignment,
                    before_conv,
                    after_conv,
                    reverse=reverse,
                )
                return info

            if not ARGS().skip_completeness:
                outfile = ARGS().output.with_suffix(".completeness.smt2")
                with open_file(outfile, "w") as dump:
                    dump.write(f";; completeness check\n".encode(SMT_ENCODING))
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
                with open_file(outfile, "w") as dump:
                    dump.write(f";; soundness check\n".encode(SMT_ENCODING))
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
                with open_file(outfile, "w") as dump:
                    dump.write(f";; check that all zero is a model\n".encode(SMT_ENCODING))
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
                with open_file(outfile, "w") as dump:
                    dump.write(
                        f";; check that all is_valid zero makes all multiplicities zero\n".encode(
                            SMT_ENCODING
                        )
                    )
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
                with open_file(outfile, "w") as dump:
                    dump.write(f";; soundness check\n".encode(SMT_ENCODING))
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
