import json

from .utils.basic_block import BasicBlock
from .smt.encoding import build_input_output_relation, collect_variables
from .smt.conversion import check_formula, convert_to_smt_formula
from .smt.utils import *

def verify(before: FNode, after: FNode, block: BasicBlock):

    before_smt, before_conv = convert_to_smt_formula("before", before, block)
    after_smt, after_conv = convert_to_smt_formula("after", after, block)

    # obtain input and output info
    inputs1 = before_conv.bus_interaction_encoder.get_inputs()
    inputs2 = after_conv.bus_interaction_encoder.get_inputs()
    outputs1 = before_conv.bus_interaction_encoder.get_outputs()
    outputs2 = after_conv.bus_interaction_encoder.get_outputs()
    iorelation = And(
        build_input_output_relation("INPUT RELATION", inputs1, inputs2),
        build_input_output_relation("OUTPUT RELATION", outputs1, outputs2),
    )


    # obtain variables and globals
    var1 = collect_variables(before_smt)
    var2 = collect_variables(after_smt)
    globals = before_smt.globals | after_smt.globals

    # check soundness
    soundness = ForAll((var1 | var2) - globals,
        And(
            Not(
                Implies(
                    And(
                        *before_smt.constraints,
                        *before_smt.bus_interactions,
                        iorelation,
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
    match check_formula(soundness):
        case False,_:
            print("Soundness is proven")
        case None,_:
            print("Could not solve formula, solver returned UNKNOWN")
        case True,model:
            print("Soundness is violated")
            model = to_nice_model(model)
            print(json.dumps(model, indent=4))

    # check completeness
    completeness = ForAll((var1 | var2) - globals,
        And(
            Not(
                Implies(
                    And(
                        *after_smt.constraints,
                        *after_smt.bus_interactions,
                        iorelation,
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
    match check_formula(completeness):
        case False,_:
            print("Completeness is proven")
        case None,_:
            print("Could not solve formula, solver returned UNKNOWN")
        case True,model:
            print("Completeness is violated")
            model = to_nice_model(model)
            print(json.dumps(model, indent=4))