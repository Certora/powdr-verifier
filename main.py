from io import StringIO
import logging
from pathlib import Path
import sys

from src.checker import check
from src.utils.basic_block import BasicBlock
from src.evaluator import evaluate
from src.utils.args import parse_args, ARGS
from src.utils.io import load_apc_dump, load_json
from src.utils.profiling import print_profile
from src.tracer import trace
from src.verifier import verify
from src.diff import diff
from src.simplifier import simplify
from src import converter
from src.encoding_analysis import analyze_aliases


if __name__ == '__main__':
    logging.basicConfig(level=logging.WARNING, force=True, format='%(levelname)s:%(relativeCreated)dms %(message)s')
    parse_args(sys.argv[1:])

    try:
        match ARGS().command:
            case 'trace':
                logging.warning(f"running tracer on {ARGS().input.relative_to(Path.cwd())}")
                trace()

            case 'eval':
                logging.warning(f"evaluating trace from {ARGS().model} on {ARGS().input.relative_to(Path.cwd())}")
                input = load_apc_dump(ARGS().input, 'input')
                model = load_json(ARGS().model, 'model')
                evaluate(input, model)

            case 'diff':
                logging.warning(f"diffing {ARGS().input_before.relative_to(Path.cwd())} and {ARGS().input_after.relative_to(Path.cwd())}")
                diff()

            case 'text':
                logging.warning(f"converting {ARGS().input.relative_to(Path.cwd())} to text")
                input = load_apc_dump(ARGS().input, 'input')
                s = StringIO()
                converter.text(s, input)
                print(s.getvalue())

            case 'simplify':
                logging.warning(f"simplifying {ARGS().input.relative_to(Path.cwd())}")
                simplify()

            case 'verify':
                logging.warning(f"verify equivalence of {ARGS().input_before.relative_to(Path.cwd())} and {ARGS().input_after.relative_to(Path.cwd())}")
                verify()
            
            case 'check':
                logging.warning(f"checking smt2 file {ARGS().input.relative_to(Path.cwd())}")
                check()
            
            case 'aliasing':
                logging.warning(f"finding aliasing in {ARGS().input.relative_to(Path.cwd())}")
                analyze_aliases()

            case _:
                logging.error(f"unknown command: {ARGS().command}")
                exit(1)
    except Exception as e:
        raise e
    finally:
        print_profile()