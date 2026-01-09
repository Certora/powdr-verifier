import logging

from src.basic_block import *
from src.encoding import *
from src.evaluator import *
from src.utils import *
from src.smt import *

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    parse_args()

    match ARGS().command:
        case 'eval':
            input = load_json(ARGS().input, 'input')
            model = load_json(ARGS().model, 'model')

            smt = convert_to_smt_formula("input", input, BasicBlock(input["block"]))

            evaluate(input["machine"], smt, model)

        case 'verify':
            before = load_json(ARGS().input_before, 'Before')
            after = load_json(ARGS().input_after, 'After')

            before_block = BasicBlock(before["block"])
            assert before_block == BasicBlock(after["block"]), "The basic block has changed"

            before_smt = convert_to_smt_formula("before", before, before_block)
            after_smt = convert_to_smt_formula("after", after, before_block)

            vc = build_vc(before_smt, after_smt)

            if check_formula(vc):
                print("The two programs are equivalent")
            else:
                print("The two programs are not equivalent")
        case _:
            logging.error(f"Unknown command: {ARGS().command}")
            exit(1)
