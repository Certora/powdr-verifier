import json

# TODO: verify determinism for a couple of examples


from .utils.basic_block import BasicBlock
from .smt.encoding import build_input_output_relation, collect_variables
from .smt.conversion import FormulaWithAxioms, SmtConverter, check_formula
from .smt.utils import *

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"

def strip_prefix(name: str) -> str:
    if name.startswith(BEFORE_PREFIX):
        return name[len(BEFORE_PREFIX)+1:]
    elif name.startswith(AFTER_PREFIX):
        return name[len(AFTER_PREFIX)+1:]
    return name

def build_model_map(old: frozenset[FNode], new: frozenset[FNode], oldf: FormulaWithAxioms, newf: FormulaWithAxioms) -> dict:
    omap = { strip_prefix(v.symbol_name()): v for v in old }
    nmap = { strip_prefix(v.symbol_name()): v for v in new }
    ndmap = { strip_prefix(v[0].symbol_name()): v for v in newf.derived }

    res = {
        k: Equals(nmap[k], omap[k]) for k in (omap.keys() & nmap.keys())
    } | {
        k: Equals(v[0], v[1]) for (k,v) in ndmap.items()
    }
    assert nmap.keys() == res.keys(), "model map for is not complete"
    return res

def do_check(f: FNode, name: str):
    match check_formula(f, name):
        case False,_:
            print(f"{name} is proven")
        case None,_:
            print(f"could not solve {name}, solver returned UNKNOWN")
        case True,model:
            print(f"{name} is violated")
            model = to_nice_model(model)
            print(json.dumps(model, indent=4))

def verify(before: FNode, after: FNode, block: BasicBlock):

    with (
        SmtConverter(BEFORE_PREFIX, block) as before_conv,
        SmtConverter(AFTER_PREFIX, block) as after_conv
    ):
        before_smt = before_conv.to_formula_with_axioms(before)
        after_smt = after_conv.to_formula_with_axioms(after)


        # obtain input and output info
        inputs1 = before_conv.bus_interaction_encoder.get_inputs()
        inputs2 = after_conv.bus_interaction_encoder.get_inputs()
        outputs1 = before_conv.bus_interaction_encoder.get_outputs()
        outputs2 = after_conv.bus_interaction_encoder.get_outputs()
        input_relation = build_input_output_relation("INPUT RELATION", inputs1, inputs2)
        output_relation = build_input_output_relation("OUTPUT RELATION", outputs1, outputs2)


    # obtain variables and globals
    var1 = collect_variables(before_smt)
    var2 = collect_variables(after_smt)
    globals = before_smt.globals | after_smt.globals

    model_map = build_model_map(var1 - globals, var2 - globals, before_smt, after_smt)

    # check completeness
    completeness = ForAll(var2 - globals,
        And(
            Not(
                Implies(
                    And(
                        *before_smt.constraints,
                        *before_smt.bus_interactions,
                        with_comment(And(*model_map.values()), "MODEL MAP"),
                    ),
                    And(
                        *after_smt.constraints,
                        *after_smt.bus_interactions,
                    )
                )
            ),
            And(*before_smt.axioms),
            And(*after_smt.axioms),
        )
    )
    do_check(completeness, "completeness")
    return

    # determinism: if an input has a trace for both programs, the outputs are the same
    determinism = And(
        Not(
            Implies(
                And(
                    *before_smt.constraints,
                    *before_smt.bus_interactions,
                    *after_smt.constraints,
                    *after_smt.bus_interactions,
                    input_relation,
                ),
                And(
                    common_intermediates,
                    output_relation
                )
            )
        ),
        And(*before_smt.axioms),
        And(*after_smt.axioms),
    )
    do_check(determinism, "determinism")

    # check soundness
    soundness =  ForAll(var1 - globals,
        And(
            Not(
                Implies(
                    And(
                        iorelation,
                        *after_smt.constraints,
                        *after_smt.bus_interactions,
                    ),
                    And(
                        *before_smt.constraints,
                        *before_smt.bus_interactions,
                    )
                )
            ),
            And(*before_smt.axioms),
            And(*after_smt.axioms),
        )
    )
    do_check(soundness, "soundness")
