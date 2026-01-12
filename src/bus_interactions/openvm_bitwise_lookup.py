import logging
from typing import Any
from pysmt.shortcuts import *
from pysmt.typing import *
from pysmt.fnode import FNode

from .single_interaction_encoder import SingleInteractionEncoder

class OpenVMBitwiseLookupEncoder(SingleInteractionEncoder):
    UF_XOR = Symbol('uf_xor', FunctionType(INT, [INT, INT]))

    def __init__(self, name: str) -> None:
        super().__init__(name)
        self.needs_xor_axioms = False
        self.globals = frozenset([self.UF_XOR])

    def encode(self, mult: Any, x: Any, y: Any, z: Any, op: Any) -> FNode:
        if op == Int(0):
            return And(
                LE(Int(0), x), LE(x, Int(255)),
                LE(Int(0), y), LE(y, Int(255)),
                Equals(z, Int(0)),
                Equals(op, Int(0)),
            )
        elif op == Int(1):
            self.needs_xor_axioms = True
            return And(
                LE(Int(0), x), LE(x, Int(255)),
                LE(Int(0), y), LE(y, Int(255)),
                Equals(Function(self.UF_XOR, [x, y]), z),
                Equals(op, Int(1)),
            )
        else:
            logging.error(f"Unsupported bitwise operation: {op}")
            return None

    def get_axioms(self) -> list[FNode]:
        if not self.needs_xor_axioms:
            return TRUE()
        x = Symbol('x', INT)
        return And(
            ForAll([x], Equals(Function(self.UF_XOR, [x, Int(0)]), x)),
            ForAll([x], Equals(Function(self.UF_XOR, [Int(0), x]), x)),
            ForAll([x], Equals(Function(self.UF_XOR, [x, x]), Int(0))),
        )
