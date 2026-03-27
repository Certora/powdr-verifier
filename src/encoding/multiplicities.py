from collections import defaultdict
import itertools
from ..smt.conversion import FormulaWithAxioms, SmtConverter
from ..smt.utils import *
from .utils import as_script

@as_script("unsat")
def encode_mult_is_zero_or_pmone(conv: SmtConverter, formula: FormulaWithAxioms) -> script.SmtLibScript:
    mults = {}
    for encoder in conv.bus_interaction_encoder.encoders:
        for id,i in enumerate(encoder._interactions):
            name = f"{encoder.NAME}#{id}"
            if encoder.STATEFUL:
                vals = frozenset([-1,0,1])
            else:
                vals = frozenset([0,1])
            
            if i.mult not in mults:
                mults[i.mult] = {
                    "values": vals,
                    "names": [name],
                }
            else:
                mults[i.mult]["names"].append(name)
                mults[i.mult]["values"] = mults[i.mult]["values"] & vals

    return And(
        *formula.constraints,
        *formula.axioms,
        Or(*[
            with_comment(
                And(
                    Not(Equals(wrap_mod(Minus(mult, Int(v))), Int(0))) for v in data["values"]
                ),
                f"{", ".join(data["names"])} in {data["values"]}"
            ) for mult,data in mults.items()
        ]),
    )

@as_script("unsat")
def encode_mult_in_pairs_if_stateful(conv: SmtConverter, formula: FormulaWithAxioms) -> script.SmtLibScript:

    pairs = defaultdict(list)
    for encoder in conv.bus_interaction_encoder.encoders:
        if not encoder.STATEFUL:
            continue
        for ((ida,a),(idb,b)) in itertools.batched(enumerate(encoder._interactions), 2, strict=True):
            f = Or(
                And(
                    Equals(wrap_mod(a.mult), Int(0)),
                    Equals(wrap_mod(b.mult), Int(0))
                ),
                And(
                    Equals(wrap_mod(Minus(a.mult, Int(1))), Int(0)),
                    Equals(wrap_mod(Plus(b.mult, Int(1))), Int(0))
                ),
            )
            name = f"{encoder.NAME}#{ida}/{idb}"
            pairs[f].append(name)
            
    return And(
        *formula.constraints,
        *formula.axioms,
        Or(*[
            Not(
                with_comment(p, f"balancing of mult for {', '.join(names)}")
            ) for p,names in pairs.items()
        ]),
    )
