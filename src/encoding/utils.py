from ..smt.utils import *

def as_script(status: str):
    def wrapped(f):
        def inner(*args, **kwargs):
            formula = f(*args, **kwargs)
            return convert_to_smt_script(formula, status)
        return inner
    return wrapped
