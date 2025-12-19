import argparse
from bz2 import decompress
from enum import Enum
import functools
import json
import logging
from typing import Any, TextIO, Optional

class BusInteractionHandlers(Enum):
    OPENVM = 'openvm'
    DEFAULT = OPENVM

    def __str__(self) -> str:
        return self.value

class OpenVMBusInteraction(Enum):
    EXECUTION_BRIDGE = 0
    MEMORY = 1
    PC_LOOKUP = 2
    VARIABLE_RANGE_CHECKER = 3
    BITWISE_LOOKUP = 6
    TUPLE_RANGE_CHECKER = 7

    def __str__(self) -> str:
        return self.value


ARGS: Optional[argparse.Namespace] = None

def args() -> argparse.Namespace:
    assert ARGS is not None
    return ARGS

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('input_before', type=argparse.FileType('r'))
    parser.add_argument('input_after', type=argparse.FileType('r'))
    parser.add_argument('--bus-interaction-handler', type=BusInteractionHandlers, default=BusInteractionHandlers.DEFAULT, choices=list(BusInteractionHandlers))
    parser.add_argument('--log-json', action='store_true')
    parser.add_argument('--log-conversion', action='store_true')
    parser.add_argument('--log-smt', action='store_true')
    parser.add_argument('--dump-smt', action='store_true')
    parser.add_argument('-v', '--verbose', action='count', default=0)
    global ARGS
    ARGS = parser.parse_args()
    if args().verbose > 0:
        logger = logging.getLogger()
        logger.setLevel(logger.level - 10 * args().verbose)

def load_json(file: TextIO, label: str) -> Any:
    data = json.load(file)
    if args().log_json:
        logging.info(f'{label}:\n{json.dumps(data, indent=2)}')
    return data

def log_conversion(level=logging.INFO):
    def decorator(func):
        @functools.wraps(func)
        def inner(self, before: Any) -> Any:
            after = func(self, before)
            if args().log_conversion: # and after is None:
                logging.log(level, f'Converted {before}\nto {after}')
            return after
        return inner
    return decorator

def iterate_recursive(data: Any) -> Any:
    match data:
        case dict():
            for value in data.values():
                yield value
                yield from iterate_recursive(value)
        case list():
            for item in data:
                yield item
                yield from iterate_recursive(item)
        case _:
            yield data

def map_recursive(data: Any, f) -> Any:
    match data:
        case dict():
            data = { k: map_recursive(v, f) for k, v in data.items() }
        case list():
            data = [ map_recursive(item, f) for item in data ]
    match f(data):
        case None: return data
        case r: return r
