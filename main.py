from io import StringIO
import json
import logging
import sys

from src.checker import check
from src.evaluator import evaluate
from src.utils.args import parse_args, ARGS
from src.utils.io import dump_json, load_apc_dump, load_json
from src.utils.profiling import print_profile
from src.tracer import trace
from src.verifier import verify
from src.diff import diff
from src.simplifier import simplify
from src.converter import convert_and_print
from src.encoding_analysis import analyze_aliases
from src.visualizer import visualize
from src.report.render import report


if __name__ == '__main__':

    logging.basicConfig(level=logging.WARNING, force=True, format='%(levelname)s:%(relativeCreated)dms %(message)s')
    parse_args(sys.argv[1:])

    res = None
    try:
        match ARGS().command:
            case 'trace':
                res = trace()

            case 'eval':
                res = evaluate()

            case 'visualize':
                visualize()

            case 'diff':
                diff()

            case 'text':
                convert_and_print()

            case 'simplify':
                res = simplify()

            case 'verify':
                res = verify()
            
            case 'check':
                res = check()
            
            case 'aliasing':
                analyze_aliases()

            case 'report':
                report()

            case _:
                logging.error(f"unknown command: {ARGS().command}")
                exit(1)
    except Exception as e:
        raise e
    finally:
        print_profile()
    
    if res is not None:
        dump_json(res, indent=4)
        sys.stdout.write("\n")
