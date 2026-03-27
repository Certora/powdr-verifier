from pathlib import Path


from ..smt.utils import *
from .trace import encode_trace, encode_trace_sanity

def encode_to_file(file: Path, encoding: script.SmtLibScript) -> None:
    with open(file, "w") as dump:
        pretty_print_smtlib(encoding, dump)
