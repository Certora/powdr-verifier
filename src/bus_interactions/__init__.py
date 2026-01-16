from enum import Enum
import logging
from typing import Any

from . import single_interaction_encoder
from . import openvm_bitwise_lookup
from . import openvm_execution_bridge
from . import openvm_memory
from . import openvm_pc_lookup
from . import openvm_variable_range_checker
from . import openvm_tuple_range_checker

from ..basic_block import BasicBlock
from ..smt_utils import *

class InteractionEncoder:
    """Base class for an encoder of arbitrary bus interactions."""
    def __init__(self, encoders: list[single_interaction_encoder.SingleInteractionEncoder]):
        self.encoders = encoders

    def encode(self, data: Any) -> FNode:
        raise NotImplementedError

    def encode_all(self, data: list[Any]) -> list[FNode]:
        return list(without_trues(self.encode(d) for d in data))

    def get_axioms(self) -> list[FNode]:
        return list(without_trues(encoder.get_axioms() for encoder in self.encoders))
    
    def get_globals(self) -> frozenset[FNode]:
        """Returns all global symbols that should not be part of any quantifier"""
        return frozenset.union(*[encoder.get_globals() for encoder in self.encoders])

class OpenVMBusInteraction(Enum):
    EXECUTION_BRIDGE = 0
    MEMORY = 1
    PC_LOOKUP = 2
    VARIABLE_RANGE_CHECKER = 3
    BITWISE_LOOKUP = 6
    TUPLE_RANGE_CHECKER = 7

    def __str__(self) -> str:
        return self.value

class OpenVMBusInteractionEncoder(InteractionEncoder):
    """Encoder for the OpenVM bus interactions."""
    def __init__(self, name: str, basic_block: BasicBlock):
        self.bitwise_lookup = openvm_bitwise_lookup.OpenVMBitwiseLookupEncoder(name)
        self.execution_bridge = openvm_execution_bridge.OpenVMExecutionBridgeEncoder(name)
        self.memory = openvm_memory.OpenVMMemoryEncoder(name)
        self.pc_lookup = openvm_pc_lookup.OpenVMPCLookupEncoder(name, basic_block)
        self.variable_range_checker = openvm_variable_range_checker.OpenVMVariableRangeCheckerEncoder(name)
        self.tuple_range_checker = openvm_tuple_range_checker.OpenVMTupleRangeCheckerEncoder(name)

        super().__init__([
            self.bitwise_lookup, self.execution_bridge, self.memory, self.pc_lookup,
            self.variable_range_checker, self.tuple_range_checker
        ])
    
    def encode(self, data: Any) -> FNode:
        match data:
            case {
                    'id': OpenVMBusInteraction.EXECUTION_BRIDGE.value,
                    'mult': mult,
                    'args': [pc, timestamp],
                }:
                return self.execution_bridge.encode(mult, pc, timestamp)
            case {
                    'id': OpenVMBusInteraction.MEMORY.value,
                    'mult': mult,
                    'args': [address_space, pointer, *data, timestamp],
                }:
                return self.memory.encode(mult, address_space, pointer, data, timestamp)
            case {
                    'id': OpenVMBusInteraction.PC_LOOKUP.value,
                    'mult': mult,
                    'args': [pc, op, a, b, c, d, e, f, g]
                }:
                return self.pc_lookup.encode(mult, pc, op, a, b, c, d, e, f, g)
            case {
                    'id': OpenVMBusInteraction.VARIABLE_RANGE_CHECKER.value,
                    'mult': mult,
                    'args': [x, bits]
                }:
                return self.variable_range_checker.encode(mult, x, bits)
            case {
                    'id': OpenVMBusInteraction.BITWISE_LOOKUP.value,
                    'mult': mult,
                    'args': [x, y, z, op]
                }:
                return self.bitwise_lookup.encode(mult, x, y, z, op)
            case {
                    'id': OpenVMBusInteraction.TUPLE_RANGE_CHECKER.value,
                    'mult': mult,
                    'args': [x, y]
                }:
                return self.tuple_range_checker.encode(mult, x, y)
            case _:
                logging.error(f"Unsupported bus interaction: {data}")
                return None

