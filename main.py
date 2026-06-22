#!/usr/bin/env python3

from io import StringIO
import cProfile
import logging
import signal
import sys

from src.checker import check
from src.evaluator import evaluate
from src.smt_backends.pysmt import disable_typecheck
from src.utils.args import parse_args, ARGS
from src.utils.io import dump_json, load_apc_dump, load_json
from src.utils.profiling import dump_cprofile, print_profile
from src.tracer import trace
from src.verifier import verify
from src.diff import diff
from src.simplifier import simplify
from src.converter import convert_and_print
from src.encoding_analysis import analyze_aliases
from src.visualizer import visualize
from src.powdr_opt import run_powdr_opt


if __name__ == '__main__':

    logging.basicConfig(level=logging.WARNING, force=True, format='%(levelname)s:%(relativeCreated)dms %(message)s')
    parse_args(sys.argv[1:])
    if ARGS().no_typecheck:
        disable_typecheck()
        logging.warning("PySMT type checking disabled")

    def run():
        res = None
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
                from src.report.render import report

                report()

            case 'powdr-opt':
                run_powdr_opt()

            case _:
                logging.error(f"unknown command: {ARGS().command}")
                exit(1)
        return res

    profiler = cProfile.Profile() if ARGS().cprofile else None
    if profiler is not None:
        def _terminate_for_profile(signum, _frame):
            raise SystemExit(128 + signum)

        signal.signal(signal.SIGTERM, _terminate_for_profile)
        profiler.enable()

    try:
        res = run()
    finally:
        if profiler is not None:
            dump_cprofile(profiler)
        print_profile()
    
    if res is not None:
        dump_json(res, indent=4)
        sys.stdout.write("\n")
