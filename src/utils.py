import argparse
from enum import Enum
import functools
import json
import logging
from pathlib import Path
from typing import Any, TextIO, Optional

class BusInteractionHandlers(Enum):
    OPENVM = 'openvm'
    DEFAULT = OPENVM

    def __str__(self) -> str:
        return self.value

class FieldTypes(Enum):
    BABYBEAR = 0x78000001
    KOALABEAR = 0x7f000001
    GOLDILOCKS = 0xFFFFFFFF00000001

    def __str__(self) -> str:
        return self.name.lower()

__ARGS: Optional[argparse.Namespace] = None

def ARGS() -> argparse.Namespace:
    assert __ARGS is not None
    return __ARGS

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', action='count', default=0)
    parser.add_argument('--bus-interaction-handler', type=BusInteractionHandlers, default=BusInteractionHandlers.DEFAULT, choices=list(BusInteractionHandlers))
    parser.add_argument('--field-type', type=FieldTypes, default=FieldTypes.BABYBEAR, choices=list(FieldTypes))
    parser.add_argument('--log-json', action='store_true')
    parser.add_argument('--log-conversion', action='store_true')
    parser.add_argument('--log-smt', action='store_true')

    sub = parser.add_subparsers(dest="command")

    sub_eval = sub.add_parser('eval')
    sub_eval.add_argument('input', type=Path)
    sub_eval.add_argument('model', type=Path)

    sub_verify = sub.add_parser('verify')
    sub_verify.add_argument('input_before', type=Path)
    sub_verify.add_argument('input_after', type=Path)
    sub_verify.add_argument('--log-rewrites', action='store_true')
    sub_verify.add_argument('--dump-smt', action='store_true')

    global __ARGS
    __ARGS = parser.parse_args()
    if ARGS().verbose > 0:
        logger = logging.getLogger()
        logger.setLevel(logger.level - 10 * ARGS().verbose)

def get_smt_dump_filename() -> Path:
    return ARGS().input_before.parent / f"verify-{ARGS().input_before.stem}-{ARGS().input_after.stem}.smt2"

def load_json(file: Path, label: str) -> Any:
    with open(file, 'r') as f:
        data = json.load(f)
    if ARGS().log_json:
        logging.info(f'{label}:\n{json.dumps(data, indent=2)}')
    return data

def log_conversion(level=logging.INFO):
    def decorator(func):
        @functools.wraps(func)
        def inner(self, before: Any) -> Any:
            after = func(self, before)
            if ARGS().log_conversion: # and after is not None:
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
