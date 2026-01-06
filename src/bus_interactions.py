import logging
from typing import Any
from pysmt.shortcuts import *
from pysmt.typing import *
from pysmt.fnode import FNode

from .smt_utils import wrap_mod
from .utils import *

class BusInteractionEncoder:

    @staticmethod
    def get_encoder() -> Any:
        match ARGS().bus_interaction_handler:
            case BusInteractionHandlers.OPENVM: return OpenVMBusInteractionEncoder()
            case _:
                logging.error(f"Unsupported bus interaction handler: {ARGS().bus_interactions}")
                return None

    @log_conversion()
    def encode(self, data: Any) -> FNode:
        raise NotImplementedError

    def get_axioms(self) -> list[FNode]:
        raise NotImplementedError

class OpenVMBusInteractionEncoder(BusInteractionEncoder):
    UF_XOR = Symbol('uf_xor', FunctionType(INT, [INT, INT]))

    def __init__(self):
        x = Symbol('x', INT)
        self.axioms = [
            ForAll([x], Equals(Function(self.UF_XOR, [x, Int(0)]), x)),
            ForAll([x], Equals(Function(self.UF_XOR, [Int(0), x]), x)),
            ForAll([x], Equals(Function(self.UF_XOR, [x, x]), Int(0))),
        ]

    @log_conversion()
    def encode(self, data: Any) -> FNode:
        match data:
            case {'mult': mult} if mult.is_int_constant() and mult.constant_value() == 0:
                return TRUE()
            case {'id': OpenVMBusInteraction.EXECUTION_BRIDGE.value}:
                return TRUE()
            case {
                    'id': OpenVMBusInteraction.MEMORY.value,
                    'mult': mult,
                    'args': [address_space, pointer, *data, timestamp],
                }:
                return Implies(
                    Equals(wrap_mod(mult), wrap_mod(Int(-1))),
                    And(
                        *[ And(LE(Int(0), d), LE(d, Int(255))) for d in data ]
                    )
                )
            case {'id': OpenVMBusInteraction.PC_LOOKUP.value}:
                return TRUE()
            case {
                    'id': OpenVMBusInteraction.VARIABLE_RANGE_CHECKER.value,
                    'mult': mult,
                    'args': [x, bits]
                }:
                curbits = 25
                if bits.is_int_constant() and bits.constant_value() <= 25:
                    curbits = bits.constant_value()

                return And(
                    LE(Int(0), x), LT(x, Int(2 ** curbits)),
                )
            case {
                    'id': OpenVMBusInteraction.BITWISE_LOOKUP.value,
                    'mult': mult,
                    'args': [x, y, z, op]
                }:
                if op == Int(0):
                    return And(
                        LE(Int(0), x), LE(x, Int(255)),
                        LE(Int(0), y), LE(y, Int(255)),
                        Equals(z, Int(0)),
                        Equals(op, Int(0)),
                    )
                elif op == Int(1):
                    print(f'Using {self.UF_XOR} to encode bitwise lookup for {x} {y} {z} {op}')
                    return And(
                        LE(Int(0), x), LE(x, Int(255)),
                        LE(Int(0), y), LE(y, Int(255)),
                        Equals(Function(self.UF_XOR, [x, y]), z),
                        Equals(op, Int(0)),
                    )
                return None
            case {'id': OpenVMBusInteraction.TUPLE_RANGE_CHECKER.value}:
                return None
            case _:
                logging.error(f"Unsupported bus interaction: {data}")
                return None
    
    def get_axioms(self) -> list[FNode]:
        return self.axioms
