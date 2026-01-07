from pysmt.fnode import FNode
from pysmt.shortcuts import *
from typing import Optional

from .utils import ARGS

UF_MOD = Symbol('uf_mod', FunctionType(INT, [INT, INT]))
REAL_MOD = Symbol('mod', FunctionType(INT, [INT, INT]))

def wrap_mod(input: FNode, modulus: Optional[FNode] = None) -> FNode:
    if modulus is None:
        modulus = Int(ARGS().field_type.value)
    return Function(UF_MOD, [input, modulus])
