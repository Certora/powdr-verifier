from collections import defaultdict
import itertools
from ..smt.conversion import FormulaWithAxioms, SmtConverter
from ..smt.utils import *
from .utils import as_script

@as_script("unsat")
def encode_timestamps_increase(conv: SmtConverter, formula: FormulaWithAxioms) -> script.SmtLibScript:
    pairs = []
    for encoder in conv.bus_interaction_encoder.encoders:
        if not encoder.TIMESTAMPED:
            continue
        for ((ida,a),(idb,b)) in itertools.batched(enumerate(encoder._interactions), 2, strict=True):
            f = Implies(
                And(
                    Not(Equals(wrap_mod(a.mult), Int(0))),
                    Not(Equals(wrap_mod(b.mult), Int(0)))
                ),
                LT(a.args[-1], b.args[-1])
            )
            name = f"{encoder.NAME}#{ida}/{idb} timestamps increase"
            pairs.append(with_comment(f, name))
            
    return And(
        *formula.constraints,
        *formula.axioms,
        Or(*pairs),
    )
