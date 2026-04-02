from collections import defaultdict
import itertools
from ..smt.conversion import FormulaWithAxioms, SmtConverter
from ..smt.utils import *

def sanity_satisfies_derived(formula: FormulaWithAxioms) -> Iterable[FNode]:
    for v, expr in formula.derived.items():
        yield with_comment(
            Not(Equals(wrap_mod(Minus(v, expr)), Int(0))),
            f"derived {v} = {expr}"
        )

def sanity_mult_values(conv: SmtConverter, formula: FormulaWithAxioms) -> Iterable[FNode]:
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

    for mult,data in mults.items():
        yield with_comment(
            And(
                Not(Equals(wrap_mod(Minus(mult, Int(v))), Int(0))) for v in data["values"]
            ),
            f"multiplicities of {", ".join(data["names"])} in {data["values"]}"
        )

def sanity_stateful_mult_pairs(conv: SmtConverter, formula: FormulaWithAxioms) -> Iterable[FNode]:
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
                    Equals(wrap_mod(Plus(a.mult, Int(1))), Int(0)),
                    Equals(wrap_mod(Minus(b.mult, Int(1))), Int(0))
                ),
            )
            name = f"{encoder.NAME}#{ida}/{idb}"
            pairs[f].append(name)

    for p,names in pairs.items():
        yield with_comment(Not(p), f"balancing of mult for {', '.join(names)}")

def sanity_timestamps_increase(conv: SmtConverter, formula: FormulaWithAxioms) -> Iterable[FNode]:
    for encoder in conv.bus_interaction_encoder.encoders:
        if not encoder.TIMESTAMPED:
            continue
        for ((ida,a),(idb,b)) in itertools.batched(enumerate(encoder._interactions), 2, strict=True):
            f = Implies(
                And(
                    Equals(wrap_mod(a.mult), Int(0)),
                    Equals(wrap_mod(b.mult), Int(0)),
                ),
                LT(a.args[-1], b.args[-1])
            )
            name = f"{encoder.NAME}#{ida}/{idb} timestamps increase"
            yield with_comment(Not(f), name)

