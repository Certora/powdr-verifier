import logging

from src.utils.basic_block import *
from src.utils.smt_encoding import *
from src.evaluator import evaluate
from src.utils.args import *
from src.utils.smt_conversion import *
from src.utils.io import load_apc_dump, load_json
from src.tracer import trace
from src.verifier import verify
from src.diff import diff


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    parse_args()

    match ARGS().command:
        case 'trace':
            logging.info(f"running tracer on {ARGS().input}")
            input = load_apc_dump(ARGS().input, 'input')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            trace(smt)

        case 'eval':
            logging.info(f"evaluating trace from {ARGS().model} on {ARGS().input}")
            input = load_apc_dump(ARGS().input, 'input')
            model = load_json(ARGS().model, 'model')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            evaluate(input["machine"], smt, model)

        case 'diff':
            logging.info(f"diffing {ARGS().input_before} and {ARGS().input_after}")
            diff()

        case 'verify':
            logging.info(f"verify equivalence of {ARGS().input_before} and {ARGS().input_after}")
            before = load_apc_dump(ARGS().input_before, 'before')
            after = load_apc_dump(ARGS().input_after, 'after')

            before_block = BasicBlock(before["block"])
            assert before_block == BasicBlock(after["block"]), "The basic block has changed"

            verify(before, after, before_block)
        case _:
            logging.error(f"unknown command: {ARGS().command}")
            exit(1)
