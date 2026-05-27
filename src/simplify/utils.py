"""Round-trip helpers between ``SmtLibScript`` objects and serialized SMT-LIB text."""
import inspect
from io import StringIO

from ..smt.utils import *

def _script_to_string(smt_script: script.SmtLibScript) -> str:
    """Serialize ``smt_script`` to a single SMT-LIB string (no pretty-print)."""
    smt2_in = StringIO()
    serialize_smtlib(smt_script, smt2_in)
    return smt2_in.getvalue()

def _string_to_script(smt2_string: str) -> script.SmtLibScript:
    """Parse SMT-LIB text into a ``SmtLibScript``."""
    parser = SmtLibParser()
    return parser.get_script(StringIO(smt2_string))

def convert_script_to_string(f):
    """Decorator: pass script as string to ``f``; replace script with parsed result (or unchanged if ``None``)."""

    def wrapped(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
        """Call underlying ``f`` with serialized input; optional ``original_script`` kw if declared."""
        kwargs = {}
        sig = inspect.signature(f)
        if sig.parameters.get("original_script") is not None:
            kwargs["original_script"] = smt_script
        if sig.parameters.get("subaction") is not None:
            kwargs["subaction"] = subaction
        res = f(_script_to_string(smt_script), **kwargs)
        if res is None:
            return smt_script
        return _string_to_script(res)
    return wrapped
