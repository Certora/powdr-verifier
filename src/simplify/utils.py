import inspect
from io import StringIO

from ..smt.utils import *

def _script_to_string(smt_script: script.SmtLibScript) -> str:
    smt2_in = StringIO()
    pretty_print_smtlib(smt_script, smt2_in)
    return smt2_in.getvalue()

def _string_to_script(smt2_string: str) -> script.SmtLibScript:
    parser = SmtLibParser()
    return parser.get_script(StringIO(smt2_string))

def convert_script_to_string(f):
    def wrapped(smt_script: script.SmtLibScript) -> script.SmtLibScript:
        kwargs = {}
        if inspect.signature(f).parameters.get("original_script") is not None:
            kwargs["original_script"] = smt_script
        res = f(_script_to_string(smt_script), **kwargs)
        if res is None:
            return smt_script
        return _string_to_script(res)
    return wrapped
