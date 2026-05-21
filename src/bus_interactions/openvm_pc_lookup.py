"""PC lookup bus: opcode and operand constraints keyed by program counter."""
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..utils.basic_block import BasicBlock
from ..smt.utils import *
from ..utils.utils import none_if


class OpenVMPCLookupEncoder(SingleInteractionEncoder):
    """
    Encodes PC lookup bus interactions. It implements a lookup table based on
    the pc into the instruction list. It retrieves the opcode and up to seven
    arguments.
    """

    UF_OPCODE = Symbol("pc_opcode", FunctionType(INT, [INT]))
    UF_A = Symbol("pc_a", FunctionType(INT, [INT]))
    UF_B = Symbol("pc_b", FunctionType(INT, [INT]))
    UF_C = Symbol("pc_c", FunctionType(INT, [INT]))
    UF_D = Symbol("pc_d", FunctionType(INT, [INT]))
    UF_E = Symbol("pc_e", FunctionType(INT, [INT]))
    UF_F = Symbol("pc_f", FunctionType(INT, [INT]))
    UF_G = Symbol("pc_g", FunctionType(INT, [INT]))

    NAME = "pc lookup"

    def __init__(self, basic_block: BasicBlock) -> None:
        """Initialize the lookup UFs and interpreters from the given `basic_block`."""
        super().__init__()
        self.basic_block = basic_block
        self.stmt_count = len(self.basic_block.instructions)
        self.needs_axioms = False
        self.globals = frozenset(
            [
                self.UF_OPCODE,
                self.UF_A,
                self.UF_B,
                self.UF_C,
                self.UF_D,
                self.UF_E,
                self.UF_F,
                self.UF_G,
            ]
        )
        self.interpreters = {
            self.UF_OPCODE: lambda pc: Int(self.basic_block.instructions[pc // 4][0]),
            self.UF_A: lambda pc: Int(self.basic_block.instructions[pc // 4][1]),
            self.UF_B: lambda pc: Int(self.basic_block.instructions[pc // 4][2]),
            self.UF_C: lambda pc: Int(self.basic_block.instructions[pc // 4][3]),
            self.UF_D: lambda pc: Int(self.basic_block.instructions[pc // 4][4]),
            self.UF_E: lambda pc: Int(self.basic_block.instructions[pc // 4][5]),
            self.UF_F: lambda pc: Int(self.basic_block.instructions[pc // 4][6]),
            self.UF_G: lambda pc: Int(self.basic_block.instructions[pc // 4][7]),
        }

    @none_if(lambda: ARGS().no_pclookup)
    def encode_pointwise(
        self,
        mult: Any,
        pc: FNode,
        op: FNode,
        a: FNode,
        b: FNode,
        c: FNode,
        d: FNode,
        e: FNode,
        f: FNode,
        g: FNode,
    ) -> FNode:
        """Constrain `(op,a..g)` to match the instruction at program counter `pc` (when enabled)."""
        self.needs_axioms = True
        return Implies(
            Not(Equals(wrap_mod(mult), Int(0))),
            And(
                Or(
                    Equals(pc, Int(k))
                    for k in self.basic_block.instructions.keys()
                ),
                Equals(Function(self.UF_OPCODE, [pc]), wrap_mod(op)),
                Equals(Function(self.UF_A, [pc]), wrap_mod(a)),
                Equals(Function(self.UF_B, [pc]), wrap_mod(b)),
                Equals(Function(self.UF_C, [pc]), wrap_mod(c)),
                Equals(Function(self.UF_D, [pc]), wrap_mod(d)),
                Equals(Function(self.UF_E, [pc]), wrap_mod(e)),
                Equals(Function(self.UF_F, [pc]), wrap_mod(f)),
                Equals(Function(self.UF_G, [pc]), wrap_mod(g)),
            ),
        )

    def _get_instruction(self, pc: int):
        """Return the concrete instruction tuple for `pc` (expects `pc` is 4-byte aligned)."""
        return self.basic_block.instructions[pc]

    def __encode_block(self) -> Iterable[FNode]:
        """Encode the full instruction table as equalities over the PC lookup UFs."""
        for id, stmt in self.basic_block.instructions.items():
            op, a, b, c, d, e, f, g = stmt
            yield with_comment(
                And(
                    Equals(Function(self.UF_OPCODE, [Int(id)]), Int(op)),
                    Equals(Function(self.UF_A, [Int(id)]), Int(a)),
                    Equals(Function(self.UF_B, [Int(id)]), Int(b)),
                    Equals(Function(self.UF_C, [Int(id)]), Int(c)),
                    Equals(Function(self.UF_D, [Int(id)]), Int(d)),
                    Equals(Function(self.UF_E, [Int(id)]), Int(e)),
                    Equals(Function(self.UF_F, [Int(id)]), Int(f)),
                    Equals(Function(self.UF_G, [Int(id)]), Int(g)),
                ),
                f"{self.NAME} axiom #{id}"
            )

    def get_axioms(self) -> Optional[FNode]:
        """Return the UF-definition axioms for the instruction table (if `encode` was used)."""
        if self.needs_axioms:
            yield from self.__encode_block()
