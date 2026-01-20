import argparse
from enum import Enum
from pathlib import Path
import itertools
import json
import logging
from typing import Any

# we assume inputs to use BabyBear
BABYBEAR_PRIME = 0x78000001
# taken from openvm rv32im/circuit/src/extension/mod.rs
TUPLE_RANGE_CHECKER_MAX_0 = 1 << 8
TUPLE_RANGE_CHECKER_MAX_1 = 8 * (1 << 8)

class OpenVMBusInteraction(Enum):
    """The openvm bus interaction ids."""
    EXECUTION_BRIDGE = 0
    MEMORY = 1
    PC_LOOKUP = 2
    VARIABLE_RANGE_CHECKER = 3
    BITWISE_LOOKUP = 6
    TUPLE_RANGE_CHECKER = 7

    def __str__(self) -> str:
        return self.value


def parse_args() -> argparse.Namespace:
    """Parse command line arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', action='count', default=0)
    parser.add_argument('input', type=Path)
    parser.add_argument('model', type=Path)

    args = parser.parse_args()
    if args.verbose > 0:
        logger = logging.getLogger()
        logger.setLevel(logger.level - 10 * args.verbose)
    return args


def pp_constraint(input: Any):
    """Pretty print a constraint."""
    match input:
        case {'expr': expr, **rest} if rest == {}:
            return pp_constraint(expr)
        case ['-', v]:
            return f"-{pp_constraint(v)}"
        case [l, '+', r]:
            return f"({pp_constraint(l)} + {pp_constraint(r)})"
        case [l, '-', r]:
            return f"({pp_constraint(l)} - {pp_constraint(r)})"
        case [l, '*', r]:
            return f"({pp_constraint(l)} * {pp_constraint(r)})"
        case {'Constant': int(value)}:
            return f"Constant({value})"
        case int(value):
            return value
        case str(name):
            return name
        case _:
            return str(input)

    
def pp_bus_interaction(input: Any):
    """Pretty print a bus interaction."""
    match input:
        case {'id': int(id), 'mult': mult, 'args': list(args)}:
            return f"{OpenVMBusInteraction(id).name} mult={pp_constraint(mult)}\n\t{[ pp_constraint(arg) for arg in args ]}"
        case _:
            return str(input)


class Evaluator:
    """Evaluate an openvm trace."""
    def __init__(self, input: dict):
        self.input = input
        self.basic_block = input['block']

    def __evaluate(self, data: Any, model: dict[str, int]) -> Any:
        """Recursively evaluate the machine on the given model."""
        match data:
            case {
                    'block': block,
                    'machine': {
                        'constraints': list(cs),
                        'bus_interactions': list(bis),
                        'derived_columns': list(dcs),
                        **rest,
                    },
                    'subs': subs
                }:
                return {
                    'block': block,
                    'machine': {
                        'constraints': [ self.__evaluate(c, model) for c in cs ],
                        'bus_interactions': [ self.__evaluate(bi, model) for bi in bis ],
                        'derived_columns': [ self.__evaluate(dc, model) for dc in dcs ],
                        **rest,
                    },
                    'subs': subs,
                }
            # constraints
            case {'expr': expr, **rest} if rest == {}:
                return self.__evaluate(expr, model)
            case ['-', v]:
                return (-self.__evaluate(v, model)) % BABYBEAR_PRIME
            case [l, '+', r]:
                return (self.__evaluate(l, model) + self.__evaluate(r, model)) % BABYBEAR_PRIME
            case [l, '-', r]:
                return (self.__evaluate(l, model) - self.__evaluate(r, model)) % BABYBEAR_PRIME
            case [l, '*', r]:
                return (self.__evaluate(l, model) * self.__evaluate(r, model)) % BABYBEAR_PRIME
            case int(value):
                return value
            case str(name):
                assert name in model, f"{name} not found in model"
                return model[name]
            
            # bus interactions
            case {'id': int(id), 'mult': mult, 'args': list(args)}:
                return {
                    'id': id,
                    'mult': self.__evaluate(mult, model),
                    'args': [ self.__evaluate(arg, model) for arg in args ],
                }
            
            # derived columns
            case [str(name), {'Constant': int(value)}]:
                return [name, value]

            case _:
               logging.error(f"can not evaluate unsupported data: {data}")
               return data

    def __verify_constraints(self, constraints: list[tuple[Any, Any]]):
        """Verify that the constraints are satisfied."""
        for (input,evald) in constraints:
            logging.debug(f'evaluating constraint {pp_constraint(input)}')
            assert evald == 0, f"constraint {pp_constraint(input)} == {evald}"
    
    def __verify_permutation(self, name: str, mults: list[Any]):
        """Verify a permutation check on a list of bus interactions."""
        for id,((m1,d1,t1),(m2,d2,t2)) in enumerate(itertools.pairwise(mults)):
            def err(msg: str):
                return f"""
{name}
    #{id}: mult={m1}, data={d1}, timestamp={t1}
    #{id+1}: mult={m2}, data={d2}, timestamp={t2}
    {msg}
"""
            if id % 2 == 0:
                assert (m1 + m2) % BABYBEAR_PRIME == 0, err(f"mults do not permute")
                assert t1 < t2, err(f"timestamp should increment")
            else:
                assert d1 == d2, err(f"data changed")
                assert t1 == t2, err(f"timestamp changed")

    def __verify_bus_interactions(self, bus_interactions: list[tuple[Any, Any]]):
        """Verify that all bus interactions constraints are satisfied."""
        ebs = []
        mems = {}
        for (input,evald) in bus_interactions:
            logging.debug(f'verifying bus interaction {pp_bus_interaction(input)}')
            def err(msg: str):
                return f"""
original:  {pp_bus_interaction(input)}
evaluated: {pp_bus_interaction(evald)}
    {msg}
"""
            match evald:
                case {
                        'id': OpenVMBusInteraction.EXECUTION_BRIDGE.value,
                        'mult': mult,
                        'args': [pc, timestamp],
                    }:
                    # verify the permutation check later
                    ebs.append((mult, pc, timestamp))
                case {
                        'id': OpenVMBusInteraction.MEMORY.value,
                        'mult': mult,
                        'args': [address_space, pointer, *data, timestamp],
                    }:
                    # verify everything is in range, then the permutation check per address space and pointer
                    assert isinstance(address_space,int), err(f"address_space not an int")
                    assert isinstance(pointer,int), err(f"address_space not an int")
                    for id,d in enumerate(data):
                        assert d >= 0 and d <= 255, err(f"data[{id}] not in 0..255")
                    if (address_space, pointer) not in mems:
                        mems[(address_space, pointer)] = []
                    mems[(address_space, pointer)].append((mult, data, timestamp))
                case {
                        'id': OpenVMBusInteraction.PC_LOOKUP.value,
                        'mult': mult,
                        'args': [pc, op, a, b, c, d, e, f, g]
                    }:
                    # verify the lookups into the basic block
                    assert pc % 4 == 0, f"pc {pc} is not a multiple of 4"
                    assert mult == 1, err(f"mult != 1")
                    assert self.basic_block['statements'][pc // 4]['opcode'] == op, err(f"opcode != {self.basic_block['statements'][pc // 4]['opcode']}")
                    assert self.basic_block['statements'][pc // 4]['a'] == a, err(f"a != {self.basic_block['statements'][pc // 4]['a']}")
                    assert self.basic_block['statements'][pc // 4]['b'] == b, err(f"b != {self.basic_block['statements'][pc // 4]['b']}")
                    assert self.basic_block['statements'][pc // 4]['c'] == c, err(f"c != {self.basic_block['statements'][pc // 4]['c']}")
                    assert self.basic_block['statements'][pc // 4]['d'] == d, err(f"d != {self.basic_block['statements'][pc // 4]['d']}")
                    assert self.basic_block['statements'][pc // 4]['e'] == e, err(f"e != {self.basic_block['statements'][pc // 4]['e']}")
                    assert self.basic_block['statements'][pc // 4]['f'] == f, err(f"f != {self.basic_block['statements'][pc // 4]['f']}")
                    assert self.basic_block['statements'][pc // 4]['g'] == g, err(f"g != {self.basic_block['statements'][pc // 4]['g']}")
                case {
                        'id': OpenVMBusInteraction.VARIABLE_RANGE_CHECKER.value,
                        'mult': mult,
                        'args': [x, bits]
                    }:
                    # verify the range of x
                    assert mult == 1, err(f"mult != 1")
                    assert x >= 0 and x <= 2**min(bits, 25)-1, err(f"x not in 0..{2**min(bits, 25)-1}")
                case {
                        'id': OpenVMBusInteraction.BITWISE_LOOKUP.value,
                        'mult': mult,
                        'args': [x, y, z, op]
                    }:
                    # verify the range of x and y and the operation on z
                    assert mult == 1, err(f"mult != 1")
                    if op == 0:
                        assert x >= 0 and x <= 255, err(f"x not in 0..255")
                        assert y >= 0 and y <= 255, err(f"y not in 0..255")
                        assert z == 0, err(f"z != 0")
                    elif op == 1:
                        assert x >= 0 and x <= 255, err(f"x not in 0..255")
                        assert y >= 0 and y <= 255, err(f"y not in 0..255")
                        assert z == x ^ y, err(f"z != x ^ y")
                case {
                        'id': OpenVMBusInteraction.TUPLE_RANGE_CHECKER.value,
                        'mult': mult,
                        'args': [x, y]
                    }:
                    # verify the range of x and y
                    assert mult == 1, err(f"mult != 1")
                    assert x >= 0 and x <= TUPLE_RANGE_CHECKER_MAX_0-1, err(f"x not in 0..{TUPLE_RANGE_CHECKER_MAX_0-1}")
                    assert y >= 0 and y <= TUPLE_RANGE_CHECKER_MAX_1-1, err(f"y not in 0..{TUPLE_RANGE_CHECKER_MAX_1-1}")

        # verify the permutation checks
        self.__verify_permutation(OpenVMBusInteraction.EXECUTION_BRIDGE.name, ebs)
        for (address_space, pointer), interactions in mems.items():
            self.__verify_permutation(f"{OpenVMBusInteraction.MEMORY.name} {address_space}@{pointer}", interactions)

    def __verify_derived_columns(self, derived_columns: list[tuple[Any, Any]], model: dict[str, int]):
        """Verify that the derived columns match the model."""
        for ([_,expr],[var,v]) in derived_columns:
            logging.debug(f'verifying derived column {var} = {pp_constraint(expr)}')
            assert v == model[var], f"derived {var} has incorrect value: {pp_constraint(expr)} != {v}"
    
    def __call__(self, model: dict[str, int]) -> Any:
        """Evaluate the trace and then verify all assumptions about the machine."""
        evald = self.__evaluate(self.input, model)

        self.__verify_constraints(zip(
            self.input['machine']['constraints'],
            evald['machine']['constraints'],
        ))
        self.__verify_bus_interactions(zip(
            self.input['machine']['bus_interactions'],
            evald['machine']['bus_interactions'],
        ))
        self.__verify_derived_columns(zip(
            self.input['machine']['derived_columns'],
            evald['machine']['derived_columns'],
        ), model)


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    args = parse_args()

    logging.info(f"evaluating trace from {args.model} on {args.input}")

    with open(args.input, 'r') as f:
        input = json.load(f)
    with open(args.model, 'r') as f:
        model = json.load(f)

    evaluator = Evaluator(input)
    evaluator(model)
