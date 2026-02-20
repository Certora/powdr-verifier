import logging
from typing import Any, Optional, TextIO

from .bus_interactions import OpenVMBusInteraction

from .utils.args import ARGS
from .utils.basic_block import BasicBlock
from .smt.conversion import SmtConverter
from .smt.utils import partial_evaluate, TRUE, Int

EMPTY_INPUT = {
    "block": None,
    "machine": {
        "constraints": [],
        "bus_interactions": [],
        "derived_columns": [],
    },
    "subs": [],
    "optimistic_constraints": [],
}


def _collect_variables(data) -> frozenset[str]:
    """Collect variable names appearing in the JSON expression format used by dumps."""
    match data:
        case [left, "+", right]:
            return _collect_variables(left) | _collect_variables(right)
        case [left, "-", right]:
            return _collect_variables(left) | _collect_variables(right)
        case [left, "*", right]:
            return _collect_variables(left) | _collect_variables(right)
        case ["-", right]:
            return _collect_variables(right)
        case int():
            return frozenset()
        case str(var):
            return frozenset([var])
        case {"id": int(), "mult": mult, "args": list(args)}:
            return _collect_variables(mult) | _collect_variables(args)
        case list(ls):
            return frozenset.union(*[_collect_variables(d) for d in ls])
        case _:
            logging.error(f"invalid data when collecting variables: {data}")


def _do_eval(eval, data):
    """Recursively apply `eval` and automatically expand lists."""
    match data:
        case list(ls):
            return [_do_eval(eval, a) for a in ls]
        case _:
            return eval(data)


def _print(out: TextIO, eval, pattern="{}", *args, ignore=TRUE()):
    """Write either original or simplified (and optionally both) renderings of `args` to `out`."""
    if eval is None:
        out.write(f"{pattern.format(*args)}\n")
    elif ARGS().only_simplified:
        evald = _do_eval(eval, list(args))
        if evald != [ignore]:
            out.write(f"{pattern.format(*evald)}\n")
    else:
        out.write(f"{pattern.format(*args)}\n")
        out.write(f"--{pattern.format(*_do_eval(eval, list(args)))}\n")


def _dump_single_conversion(out: TextIO, data: Any, basic_block: BasicBlock, eval):
    """Convert a single APC dump fragment and emit its constraints/interactions/axioms/derived."""
    with SmtConverter("tmp", basic_block) as conv:
        formula = conv.to_formula_with_axioms(data)
        for c in formula.constraints:
            _print(out, eval, "->\t{}", c)
        for b in formula.bus_interactions:
            _print(out, eval, "->\t{}", b)
        for a in formula.axioms:
            _print(out, eval, "->\t{}", a)
        for k,v in formula.derived.items():
            _print(out, eval, f"->\t{k} == {v}")


def _text_bus_interaction(out: TextIO, bis: list, conv: SmtConverter, eval):
    """Pretty-print bus interactions, grouped by bus id, including per-interaction and collective encodings."""
    for val in OpenVMBusInteraction:
        bs = [bi for bi in bis if bi["id"] == val.value]
        if not bs:
            continue
        out.write(f"// Bus {val} ({val.name})\n")

        for b in bs:
            mc = conv.convert_manual(b["mult"])
            ac = [conv.convert_manual(a) for a in b["args"]]
            _print(out, eval, "\tmult={}, args={}", mc, ac)
            if ARGS().with_encoding:
                input = EMPTY_INPUT
                input["machine"]["bus_interactions"] = [b]
                _dump_single_conversion(out, input, conv.basic_block, eval)
                out.write("\n")

        if ARGS().with_encoding:
            out.write(f"collective encoding for Bus {val} ({val.name}):\n")
            input = EMPTY_INPUT
            input["machine"]["bus_interactions"] = bs
            _dump_single_conversion(out, input, conv.basic_block, eval)
        out.write("\n")


def _text_constraints(out: TextIO, cs: list, conv: SmtConverter, eval):
    """Pretty-print converted constraints (optionally simplified/evaluated under a model)."""
    out.write("constraints:\n")
    for c in cs:
        converted = conv.convert_manual(c)
        _print(out, eval, "\t{}", converted, ignore=Int(0))


def text(out: TextIO, input: dict, model: Optional[dict[str, Any]] = None):
    """Render an APC dump to a human-readable text format (optionally evaluated under `model`)."""

    match input:
        # general json structure
        case {
            "block": _,
            "machine": {
                "constraints": list(cs),
                "bus_interactions": list(bis),
                "derived_columns": list(),
                **rest_machine,
            },
            "subs": _,
            "optimistic_constraints": _,
            **rest_apc,
        }:
            assert not rest_machine
            assert not rest_apc

            block = BasicBlock(input["block"])
            with SmtConverter("tmp", block) as conv:
                eval = None
                if model is not None:
                    eval = lambda f: partial_evaluate(
                        f, model, conv.bus_interaction_encoder.get_interpreters()
                    )

                variables = _collect_variables([cs, bis])
                out.write("variables:\n")
                for var in sorted(variables):
                    out.write(f"\t{var}\n")
                out.write("\n")

                _text_bus_interaction(out, bis, conv, eval)
                _text_constraints(out, cs, conv, eval)

        case _:
            logging.error("unsupported input for text conversion")
