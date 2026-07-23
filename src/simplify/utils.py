"""Round-trip helpers between ``SmtLibScript`` objects and serialized SMT-LIB bytes."""
import inspect
from io import BytesIO, StringIO

from ..utils.io import SMT_ENCODING
from ..smt.utils import *


def _script_to_bytes(smt_script: script.SmtLibScript) -> bytes:
    buf = BytesIO()
    serialize_smtlib(smt_script, buf)
    return buf.getvalue()


def _script_to_string(smt_script: script.SmtLibScript) -> str:
    return _script_to_bytes(smt_script).decode(SMT_ENCODING)


def _bytes_to_script(smt2: bytes | str) -> script.SmtLibScript:
    parser = SmtLibParser()
    if isinstance(smt2, bytes):
        smt2 = smt2.decode(SMT_ENCODING)
    return parser.get_script(StringIO(smt2))


def _string_to_script(smt2_string: str) -> script.SmtLibScript:
    return _bytes_to_script(smt2_string.encode(SMT_ENCODING))


def convert_script_to_string(f):
    """Decorator: pass script as string to ``f``; replace script with parsed result (or unchanged if ``None``)."""

    def wrapped(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
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
