import argparse
import logging
from pathlib import Path
from typing import Optional

from .bus_interaction_handlers import BusInteractionHandlers
from .field_types import FieldTypes

__ARGS: Optional[argparse.Namespace] = None

def ARGS() -> argparse.Namespace:
    """Retrieve the command line arguments."""
    assert __ARGS is not None
    return __ARGS

def parse_args():
    """Parse the command line arguments."""
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', action='count', default=0)
    parser.add_argument('--bus-interaction-handler', type=BusInteractionHandlers, default=BusInteractionHandlers.DEFAULT, choices=list(BusInteractionHandlers))
    parser.add_argument('--field-type', type=FieldTypes, default=FieldTypes.BABYBEAR, choices=list(FieldTypes))
    parser.add_argument('--log-conversion', action='store_true')
    parser.add_argument('--log-json', action='store_true')
    parser.add_argument('--log-rewrites', action='store_true')
    parser.add_argument('--log-smt', action='store_true')
    parser.add_argument('--log-memory-analysis', action='store_true')
    parser.add_argument('--dump-smt', action='store_true')
    parser.add_argument('--base-dump', type=Path, default=None)

    sub = parser.add_subparsers(dest="command")
    
    sub_trace = sub.add_parser('trace')
    sub_trace.add_argument('input', type=Path)
    sub_trace.add_argument('--use-derived', action='store_true')
    sub_trace.add_argument('--dump-model', type=Path, default=None)

    sub_eval = sub.add_parser('eval')
    sub_eval.add_argument('input', type=Path)
    sub_eval.add_argument('model', type=Path)

    sub_diff = sub.add_parser('diff')
    sub_diff.add_argument('input_before', type=Path)
    sub_diff.add_argument('input_after', type=Path)

    sub_verify = sub.add_parser('verify')
    sub_verify.add_argument('input_before', type=Path)
    sub_verify.add_argument('input_after', type=Path)

    global __ARGS
    __ARGS = parser.parse_args()
    if ARGS().verbose > 0:
        logger = logging.getLogger()
        logger.setLevel(logger.level - 10 * ARGS().verbose)
    
    match ARGS().command:
        case 'trace':
            ARGS().smt_dump_filename = ARGS().input.parent / f"trace-{ARGS().input.stem}.smt2"
        case 'verify':
            ARGS().smt_dump_filename = ARGS().input_before.parent / f"verify-{ARGS().input_before.stem}-{ARGS().input_after.stem}.smt2"
        case _:
            pass
