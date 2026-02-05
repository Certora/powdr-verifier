import logging
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..utils.basic_block import BasicBlock
from ..smt.utils import *

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
        self.interpreters = {
            self.UF_OPCODE: lambda pc: Int(self.basic_block.statements[pc//4][0]),
            self.UF_A: lambda pc: Int(self.basic_block.statements[pc//4][1]),
            self.UF_B: lambda pc: Int(self.basic_block.statements[pc//4][2]),
            self.UF_C: lambda pc: Int(self.basic_block.statements[pc//4][3]),
            self.UF_D: lambda pc: Int(self.basic_block.statements[pc//4][4]),
            self.UF_E: lambda pc: Int(self.basic_block.statements[pc//4][5]),
            self.UF_F: lambda pc: Int(self.basic_block.statements[pc//4][6]),
            self.UF_G: lambda pc: Int(self.basic_block.statements[pc//4][7]),
        }

    @attach_comment("PC LOOKUP for {2}")
    def encode(self, mult: Any, pc: FNode, op: FNode, a: FNode, b: FNode, c: FNode, d: FNode, e: FNode, f: FNode, g: FNode) -> FNode:
        self.needs_axioms = True
        return Implies(
            Not(Equals(mult, Int(0))),
            And(
                LT(pc, Int(4*self.stmt_count - 3)),
                Equals(wrap_mod(pc, Int(4)), Int(0)),
                Equals(Function(self.UF_OPCODE, [pc]), wrap_mod(op)),
                Equals(Function(self.UF_A, [pc]), wrap_mod(a)),
                Equals(Function(self.UF_B, [pc]), wrap_mod(b)),
                Equals(Function(self.UF_C, [pc]), wrap_mod(c)),
                Equals(Function(self.UF_D, [pc]), wrap_mod(d)),
                Equals(Function(self.UF_E, [pc]), wrap_mod(e)),
                Equals(Function(self.UF_F, [pc]), wrap_mod(f)),
                Equals(Function(self.UF_G, [pc]), wrap_mod(g)),
            )
        )
    
    def __encode_block(self) -> Iterable[FNode]:
        for pc,stmt in enumerate(self.basic_block.statements):
            op,a,b,c,d,e,f,g = stmt
            yield And(
                Equals(Function(self.UF_OPCODE, [Int(4*pc)]), Int(op)),
                Equals(Function(self.UF_A, [Int(4*pc)]), Int(a)),
                Equals(Function(self.UF_B, [Int(4*pc)]), Int(b)),
                Equals(Function(self.UF_C, [Int(4*pc)]), Int(c)),
                Equals(Function(self.UF_D, [Int(4*pc)]), Int(d)),
                Equals(Function(self.UF_E, [Int(4*pc)]), Int(e)),
                Equals(Function(self.UF_F, [Int(4*pc)]), Int(f)),
                Equals(Function(self.UF_G, [Int(4*pc)]), Int(g)),
            )

    @attach_comment("PC LOOKUP definition")
    def get_axioms(self) -> Optional[FNode]:
        if not self.needs_axioms:
            return None
        return And(*self.__encode_block())
