from collections import defaultdict
from dataclasses import dataclass
import dataclasses
from termcolor import colored
from typing import Any


from .bus_interactions import OpenVMBusInteraction
from .smt.conversion import SmtConverter
from .smt.utils import *
from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, load_json

def highlight(value: Any) -> str:
    return colored(value, attrs=["bold"])

def opaque(value: Any) -> str:
    return colored(value, "red", attrs=["dark"])

def mod(x):
    return x % 2013265921

@dataclass
class VisualizedInteraction:
    bus: str
    key: tuple[int]
    mult: Any
    mult_eval: int
    args: tuple[Any]
    args_eval: tuple[int]
    timestamp: int
    additional: str = ""

def balancing(a: VisualizedInteraction, b: VisualizedInteraction) -> bool:
    return a.bus == b.bus and a.key == b.key and \
        mod(a.mult_eval + b.mult_eval) == 0 and \
        a.args_eval == b.args_eval

def __flatten(args) -> list[Any]:
    def inner(args) -> list[Any]:
        if isinstance(args, list) or isinstance(args, tuple):
            for a in args:
                yield from inner(a)
        else:
            yield args
    return tuple(inner(args))

def _render_bus_contents(bus_contents: dict[int, dict[tuple[Any, ...], int]]) -> str:
    lines = []
    for bus in sorted(bus_contents):
        entries = bus_contents[bus]
        if not entries:
            continue
        lines.append(f"  {bus}:")
        for payload, cnt in sorted(entries.items(), key=lambda x: str(x[0])):
            lines.append(f"    {cnt}x {list(payload)}")
    if not lines:
        return "  <empty>"
    return "\n".join(lines)


def visualize():
    """Print a timestamp-ordered interaction trace and bus contents after each step."""

    input = load_apc_dump(ARGS().input)
    model = load_json(ARGS().model)

    interactions: list[VisualizedInteraction] = []

    with SmtConverter(ARGS().var_prefix, BasicBlock(input["block"])) as conv:
        conv.to_formula_with_axioms(input)
        interpreters = conv.bus_interaction_encoder.get_interpreters()
        eval_fn = lambda f: partial_evaluate(f, model, interpreters).constant_value()

        for encoder in conv.bus_interaction_encoder.encoders:
            if not encoder.TIMESTAMPED:
                continue
            if ARGS().bus and encoder.NAME not in ARGS().bus:
                continue
            for interaction in encoder._interactions:
                args = __flatten(interaction.args)
                args_eval=tuple(eval_fn(arg) for arg in args)
                match encoder.NAME:
                    case "memory":
                        key = (encoder.NAME, args_eval[0], args_eval[1])
                        args = args[2:]
                        args_eval = args_eval[2:]
                    case "execution bridge": key = (encoder.NAME, )
                    case _: raise ValueError(f"Unsupported bus interaction: {encoder.NAME}")
                interactions.append(
                    VisualizedInteraction(
                        bus=encoder.NAME,
                        key=key,
                        mult=interaction.mult,
                        mult_eval=eval_fn(interaction.mult),
                        args=args,
                        args_eval=args_eval,
                        timestamp=eval_fn(interaction.args[-1]),
                    )
                )

        interactions.sort(key=lambda x: x.timestamp)

    inputs: dict[tuple, VisualizedInteraction] = {}
    bus_contents: dict[tuple, VisualizedInteraction] = defaultdict(lambda: defaultdict(int))
    for it in interactions:
        if it.mult_eval == 0:
            continue
        if it.key in bus_contents:
            if balancing(it, bus_contents[it.key]):
                del bus_contents[it.key]
            else:
                if it.key in inputs:
                    raise ValueError(f"Input for {it.key} already exists")
                else:
                    old = bus_contents[it.key]
                    inputs[it.key] = dataclasses.replace(old, mult_eval=mod(-old.mult_eval), additional="PRE")
                    bus_contents[it.key] = it
        else:
            bus_contents[it.key] = it

    outputs: dict[tuple, VisualizedInteraction] = {
        k: dataclasses.replace(v, mult_eval=mod(-v.mult_eval), additional="POST")
        for k, v in bus_contents.items()
    }

    interactions = [
        *inputs.values(),
        *interactions,
        *outputs.values()
    ]
        
    bus_contents: dict[tuple, VisualizedInteraction] = defaultdict(lambda: defaultdict(int))
    for it in interactions:
        if it.mult_eval != 0:
            if it.key in bus_contents:
                assert balancing(it, bus_contents[it.key])
                del bus_contents[it.key]
            else:
                bus_contents[it.key] = it

        print(f"{it.bus} {f"({it.additional}) " if it.additional else ""} ts: {it.timestamp} mult: {it.mult_eval} {opaque(it.mult)}")
        if len(it.key) > 1:
            print(f"\t{it.key[1:]} -> {it.args_eval} {opaque(it.args)}")
        else:
            print(f"\t{it.args_eval} {opaque(it.args)}")

        print("")
        print("\tcurrent bus contents:")
        if bus_contents:
            for v in bus_contents.values():
                if len(v.key) > 1:
                    print(f"\t{v.mult_eval} x {v.bus}@{v.key[1:]} -> {v.args_eval}")
                else:
                    print(f"\t{v.mult_eval} x {v.bus} -> {v.args_eval}")
        else:
            print("\t<empty>")
        
        print("")
