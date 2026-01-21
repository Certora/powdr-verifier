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
    parser.add_argument('--base-dump', type=Path, default=None)
    parser.add_argument('input', type=Path)
    parser.add_argument('model', type=Path)

    args = parser.parse_args()
    if args.verbose > 0:
        logger = logging.getLogger()
        logger.setLevel(logger.level - 10 * args.verbose)
    return args


def load_json(file: Path) -> Any:
    """Load a json file and return the data. Use label for logging."""
    with open(file, 'r') as f:
        data = json.load(f)
    return data

def load_apc_dump(file: Path, args: argparse.Namespace) -> Any:
    """
    Load an apc dump and return the data. Use label for logging.
    If the json is just the machine and not the whole apc dump,
    take the apc from the base dump and only update the machine.
    """
    data = load_json(file)
    if 'block' not in data:
        if args.base_dump is not None:
            base_data = load_json(args.base_dump)
            assert 'block' in base_data, 'no block found in base dump'
            data = base_data |  { 'machine': data }
            logging.debug(f'took block from {args.base_dump}')
        else:
            logging.error('no block found and no base dump provided')
    return data


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
                    rop,ra,rb,rc,rd,re,rf,rg = self.basic_block['statements'][pc // 4]
                    assert pc % 4 == 0, f"pc {pc} is not a multiple of 4"
                    assert mult == 1, err(f"mult != 1")
                    assert rop == op, err(f"opcode != {rop}")
                    assert ra == a, err(f"a != {ra}")
                    assert rb == b, err(f"b != {rb}")
                    assert rc == c, err(f"c != {rc}")
                    assert rd == d, err(f"d != {rd}")
                    assert re == e, err(f"e != {re}")
                    assert rf == f, err(f"f != {rf}")
                    assert rg == g, err(f"g != {rg}")
                case {
                        'id': OpenVMBusInteraction.VARIABLE_RANGE_CHECKER.value,
                        'mult': mult,
                        'args': [x, bits]
                    }:
                    # verify the range of x
                    if mult != 1:
                        logging.warning(err(f"mult != 1"))
                    assert x >= 0 and x <= 2**min(bits, 25)-1, err(f"x not in 0..{2**min(bits, 25)-1}")
                case {
                        'id': OpenVMBusInteraction.BITWISE_LOOKUP.value,
                        'mult': mult,
                        'args': [x, y, z, op]
                    }:
                    # verify the range of x and y and the operation on z
                    if mult != 1:
                        logging.warning(err(f"mult != 1"))
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
                    if mult != 1:
                        logging.warning(err(f"mult != 1"))
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
            if v != model[var]:
                logging.warning(f"derived {var} has incorrect value: {pp_constraint(expr)} != {v}")
    
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

    input = load_apc_dump(args.input, args)
    model = load_json(args.model)

    evaluator = Evaluator(input)
    evaluator(model)
