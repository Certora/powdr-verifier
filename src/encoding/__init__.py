from pathlib import Path


from ..smt.utils import *
from .trace import encode_trace, encode_trace_satisfies_derived
from .multiplicities import encode_mult_is_zero_or_pmone, encode_mult_in_pairs_if_stateful
from .timestamps import encode_timestamps_increase

def encode_to_file(file: Path, encoding: script.SmtLibScript) -> None:
    with open(file, "w") as dump:
        pretty_print_smtlib(encoding, dump)
