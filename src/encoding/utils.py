"""Encoding helpers: wrap formulas as scripts and locate ``is_valid`` symbols."""
from ..smt.utils import *

def as_script(status: str):
    def wrapped(f):
        def inner(*args, **kwargs):
            formula = f(*args, **kwargs)
            return convert_to_smt_script(formula, status)
        return inner
    return wrapped

def get_is_valid(vars: frozenset[FNode], prefix: str) -> FNode | None:
    match [v for v in vars if v.symbol_name().startswith(f"{prefix}-is_valid@")]:
        case []:
            return None
        case [is_valid]:
            return is_valid
        case _:
            logging.warning("multiple is_valid variables found, this is not supported")
            return None
