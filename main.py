import logging

from src.basic_block import *
from src.encoding import *
from src.evaluator import evaluate
from src.utils import *
from src.smt import *
from src.tracer import trace
from src.verifier import verify

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    parse_args()

    match ARGS().command:
        case 'trace':
            logging.info(f"running tracer on {ARGS().input}")
            input = load_json(ARGS().input, 'input')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            trace(smt)

        case 'eval':
            logging.info(f"evaluating trace from {ARGS().model} on {ARGS().input}")
            input = load_json(ARGS().input, 'input')
            model = load_json(ARGS().model, 'model')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            evaluate(input["machine"], smt, model)

        case 'verify':
            logging.info(f"verify equivalence of {ARGS().input_before} and {ARGS().input_after}")
            before = load_json(ARGS().input_before, 'Before')
            after = load_json(ARGS().input_after, 'After')

            before_block = BasicBlock(before["block"])
            assert before_block == BasicBlock(after["block"]), "The basic block has changed"

            verify(before, after, before_block)
        case _:
            logging.error(f"unknown command: {ARGS().command}")
            exit(1)
