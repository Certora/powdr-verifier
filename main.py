import logging
import pprint

from src.checks import *
from src.utils import *
from src.smt import *

if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    parse_args()
    before = load_json(ARGS().input_before, 'Before')
    after = load_json(ARGS().input_after, 'After')

    before_i2n, before_n2i = collect_variables(before)
    after_i2n, after_n2i = collect_variables(after)

    before_smt = load_smt_formula(before)
    after_smt = load_smt_formula(after)

    if is_equivalent(before_smt, after_smt):
        print("The two programs are equivalent")
    else:
        print("The two programs are not equivalent")
