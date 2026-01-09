import argparse
from enum import Enum
import logging
from typing import Any

from pysmt.fnode import FNode
from pysmt.shortcuts import *

from . import single_interaction_encoder
from . import openvm_bitwise_lookup
from . import openvm_execution_bridge
from . import openvm_memory
from . import openvm_pc_lookup
from . import openvm_variable_range_checker
from . import openvm_tuple_range_checker

from ..basic_block import BasicBlock

class InteractionEncoder:
    def __init__(self, encoders: list[single_interaction_encoder.SingleInteractionEncoder]):
        self.encoders = encoders

    def encode(self, data: Any) -> FNode:
        raise NotImplementedError

    def encode_all(self, data: list[Any]) -> FNode:
        return And(*[ self.encode(d) for d in data ])

    def get_axioms(self) -> list[FNode]:
        return And(*[ encoder.get_axioms() for encoder in self.encoders ])

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
            case {'id': OpenVMBusInteraction.EXECUTION_BRIDGE.value}:
                return self.execution_bridge.encode()
            case {
                    'id': OpenVMBusInteraction.MEMORY.value,
                    'mult': mult,
                    'args': [address_space, pointer, *data, timestamp],
                }:
                return self.memory.encode(mult, address_space, pointer, data, timestamp)
            case {
                    'id': OpenVMBusInteraction.PC_LOOKUP.value,
                    'mult': mult,
                    'args': operands
                }:
                return self.pc_lookup.encode(mult, operands)
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

            case {'id': OpenVMBusInteraction.TUPLE_RANGE_CHECKER.value}:
                return self.tuple_range_checker.encode()
            case _:
                logging.error(f"Unsupported bus interaction: {data}")
                return None
