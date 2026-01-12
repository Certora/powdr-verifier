import logging
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..basic_block import BasicBlock
from ..smt_utils import *

class OpenVMPCLookupEncoder(SingleInteractionEncoder):
    UF_OPCODE = Symbol('pc_opcode', FunctionType(INT, [INT]))
    UF_A = Symbol('pc_a', FunctionType(INT, [INT]))
    UF_B = Symbol('pc_b', FunctionType(INT, [INT]))
    UF_C = Symbol('pc_c', FunctionType(INT, [INT]))
    UF_D = Symbol('pc_d', FunctionType(INT, [INT]))
    UF_E = Symbol('pc_e', FunctionType(INT, [INT]))
    UF_F = Symbol('pc_f', FunctionType(INT, [INT]))
    UF_G = Symbol('pc_g', FunctionType(INT, [INT]))

    def __init__(self, name: str, basic_block: BasicBlock) -> None:
        super().__init__(name)
        self.basic_block = basic_block
        self.stmt_count = len(self.basic_block.statements)
        self.needs_axioms = False
        self.globals = frozenset([self.UF_OPCODE, self.UF_A, self.UF_B, self.UF_C, self.UF_D, self.UF_E, self.UF_F, self.UF_G])

    def encode(self, mult: Any, operands: list[Any]) -> FNode:
        match operands:
            case [pc, op, a, b, c, d, e, f, g]:
                self.needs_axioms = True
                return And(
                    LT(pc, Int(self.stmt_count)),
                    Equals(Function(self.UF_OPCODE, [pc]), op),
                    Equals(Function(self.UF_A, [pc]), a),
                    Equals(Function(self.UF_B, [pc]), b),
                    Equals(Function(self.UF_C, [pc]), c),
                    Equals(Function(self.UF_D, [pc]), d),
                    Equals(Function(self.UF_E, [pc]), e),
                    Equals(Function(self.UF_F, [pc]), f),
                    Equals(Function(self.UF_G, [pc]), g),
                )
            case _:
                logging.error(f"Unsupported operands: {operands}")
                return None

    def get_axioms(self) -> list[FNode]:
        if not self.needs_axioms:
            return TRUE()
        return And(
            And(
                Equals(Function(self.UF_OPCODE, [Int(pc)]), Int(stmt["opcode"])),
                Equals(Function(self.UF_A, [Int(pc)]), Int(stmt["a"])),
                Equals(Function(self.UF_B, [Int(pc)]), Int(stmt["b"])),
                Equals(Function(self.UF_C, [Int(pc)]), Int(stmt["c"])),
                Equals(Function(self.UF_D, [Int(pc)]), Int(stmt["d"])),
                Equals(Function(self.UF_E, [Int(pc)]), Int(stmt["e"])),
                Equals(Function(self.UF_F, [Int(pc)]), Int(stmt["f"])),
                Equals(Function(self.UF_G, [Int(pc)]), Int(stmt["g"])),
            ) for pc,stmt in enumerate(self.basic_block.statements)
        )
