"""Serialize ``FormulaWithAxioms`` to SMT-LIB files using ``pretty_print_smtlib``."""
from pathlib import Path


from ..smt.utils import *
from .trace import encode_trace, encode_trace_sanity

def encode_to_file(file: Path, encoding: script.SmtLibScript) -> None:
    """Pretty-print ``encoding`` (commands) to ``file`` as SMT-LIB."""
    with open(file, "w") as dump:
        pretty_print_smtlib(encoding, dump)
