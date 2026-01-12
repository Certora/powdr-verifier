from pysmt.fnode import FNode
from pysmt import logics, operators, substituter
from pysmt.shortcuts import *
from pysmt.smtlib import script
from pysmt.substituter import FunctionInterpretation
from typing import Any, Optional

from .utils import ARGS

UF_MOD = Symbol('uf_mod', FunctionType(INT, [INT, INT]))
REAL_MOD = Symbol('mod', FunctionType(INT, [INT, INT]))

logics.PYSMT_LOGICS = logics.PYSMT_LOGICS | frozenset([logics.QF_UFNIA, logics.UFNIA])

def wrap_mod(input: FNode, modulus: Optional[FNode] = None) -> FNode:
    if modulus is None:
        modulus = Int(ARGS().field_type.value)
    return Function(UF_MOD, [input, modulus])

def as_constant(f: FNode) -> Any:
    if f.is_constant():
        return f.constant_value()
    return str(f)

def to_nice_model(model: Any) -> dict[str, Any]:
    return {
        str(k): as_constant(v) for k,v in sorted(model, key=lambda x: str(x))
    }
