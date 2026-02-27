from io import StringIO

from ..smt.utils import *

def __script_to_string(smt_script: script.SmtLibScript) -> str:
    smt2_in = StringIO()
    pretty_print_smtlib(smt_script, smt2_in)
    return smt2_in.getvalue()

def __string_to_script(smt2_string: str) -> script.SmtLibScript:
    parser = SmtLibParser()
    return parser.get_script(StringIO(smt2_string))

def convert_script_to_string(f):
    def wrapped(smt_script: script.SmtLibScript) -> script.SmtLibScript:
        res = f(__script_to_string(smt_script))
        if res is None:
            return smt_script
        return __string_to_script(res)
    return wrapped
