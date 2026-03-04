from io import StringIO
import logging
import sys

from src.checker import check
from src.evaluator import evaluate
from src.utils.args import parse_args, ARGS
from src.utils.io import load_apc_dump, load_json
from src.utils.profiling import print_profile
from src.tracer import trace
from src.verifier import verify
from src.diff import diff
from src.simplifier import simplify
from src.converter import convert_to_text
from src.encoding_analysis import analyze_aliases


if __name__ == '__main__':

    print(" ".join(sys.argv))

    logging.basicConfig(level=logging.WARNING, force=True, format='%(levelname)s:%(relativeCreated)dms %(message)s')
    parse_args(sys.argv[1:])

    try:
        match ARGS().command:
            case 'trace':
                trace()

            case 'eval':
                input = load_apc_dump(ARGS().input, 'input')
                model = load_json(ARGS().model, 'model')
                evaluate(input, model)

            case 'diff':
                diff()

            case 'text':
                convert_to_text()

            case 'simplify':
                simplify()

            case 'verify':
                verify()
            
            case 'check':
                check()
            
            case 'aliasing':
                analyze_aliases()

            case _:
                logging.error(f"unknown command: {ARGS().command}")
                exit(1)
    except Exception as e:
        raise e
    finally:
        print_profile()