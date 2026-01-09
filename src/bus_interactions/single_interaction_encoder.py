from pysmt.fnode import FNode
from pysmt.shortcuts import *

class SingleInteractionEncoder:
    def get_axioms(self) -> list[FNode]:
        return TRUE()
