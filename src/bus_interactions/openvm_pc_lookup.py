import logging
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..basic_block import BasicBlock
from ..smt_utils import *

class OpenVMPCLookupEncoder(SingleInteractionEncoder):
    """
    Encodes PC lookup bus interactions. It implements a lookup table based on
    the pc into the instruction list. It retrieves the opcode and up to seven
    arguments.
    """
    UF_OPCODE = Symbol('pc_opcode', FunctionType(INT, [INT]))
    UF_A = Symbol('pc_a', FunctionType(INT, [INT]))
    UF_B = Symbol('pc_b', FunctionType(INT, [INT]))
    UF_C = Symbol('pc_c', FunctionType(INT, [INT]))
    UF_D = Symbol('pc_d', FunctionType(INT, [INT]))
    UF_E = Symbol('pc_e', FunctionType(INT, [INT]))
    UF_F = Symbol('pc_f', FunctionType(INT, [INT]))
    UF_G = Symbol('pc_g', FunctionType(INT, [INT]))

    def __init__(self, basic_block: BasicBlock) -> None:
        super().__init__()
        self.basic_block = basic_block
        self.stmt_count = len(self.basic_block.statements)
        self.needs_axioms = False
        self.globals = frozenset([self.UF_OPCODE, self.UF_A, self.UF_B, self.UF_C, self.UF_D, self.UF_E, self.UF_F, self.UF_G])

    def encode(self, mult: Any, pc: FNode, op: FNode, a: FNode, b: FNode, c: FNode, d: FNode, e: FNode, f: FNode, g: FNode) -> FNode:
        self.needs_axioms = True
        return And(
            LT(pc, Int(4*self.stmt_count - 3)),
            Equals(wrap_mod(pc, Int(4)), Int(0)),
            Equals(Function(self.UF_OPCODE, [pc]), op),
            Equals(Function(self.UF_A, [pc]), a),
            Equals(Function(self.UF_B, [pc]), b),
            Equals(Function(self.UF_C, [pc]), c),
            Equals(Function(self.UF_D, [pc]), d),
            Equals(Function(self.UF_E, [pc]), e),
            Equals(Function(self.UF_F, [pc]), f),
            Equals(Function(self.UF_G, [pc]), g),
        )

    def get_axioms(self) -> list[FNode]:
        if not self.needs_axioms:
            return TRUE()
        return And(
            with_comment(
                And(
                    Equals(Function(self.UF_OPCODE, [Int(4*pc)]), Int(stmt["opcode"])),
                    Equals(Function(self.UF_A, [Int(4*pc)]), Int(stmt["a"])),
                    Equals(Function(self.UF_B, [Int(4*pc)]), Int(stmt["b"])),
                    Equals(Function(self.UF_C, [Int(4*pc)]), Int(stmt["c"])),
                    Equals(Function(self.UF_D, [Int(4*pc)]), Int(stmt["d"])),
                    Equals(Function(self.UF_E, [Int(4*pc)]), Int(stmt["e"])),
                    Equals(Function(self.UF_F, [Int(4*pc)]), Int(stmt["f"])),
                    Equals(Function(self.UF_G, [Int(4*pc)]), Int(stmt["g"])),
                ),
                f"PC LOOKUP for {pc}"
            ) for pc,stmt in enumerate(self.basic_block.statements)
        )
