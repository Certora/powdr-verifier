import logging

from src.utils import *
from src.smt import *
from src.encoding import *

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    parse_args()
    before = load_json(ARGS().input_before, 'Before')
    after = load_json(ARGS().input_after, 'After')

    before_smt = convert_to_smt_formula(before)
    after_smt = convert_to_smt_formula(after)

    vc = build_vc(before_smt, after_smt)

    if check_formula(vc):
        print("The two programs are equivalent")
    else:
        print("The two programs are not equivalent")
