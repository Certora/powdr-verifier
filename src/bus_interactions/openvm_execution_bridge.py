import logging
from typing import Any
from pysmt.shortcuts import *
from pysmt.typing import *
from pysmt.fnode import FNode

from .single_interaction_encoder import SingleInteractionEncoder

class OpenVMExecutionBridgeEncoder(SingleInteractionEncoder):
    def encode(self) -> FNode:
        return TRUE()
