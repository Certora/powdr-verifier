from pysmt.fnode import FNode
from pysmt.shortcuts import *

class SingleInteractionEncoder:
    def __init__(self, name: str):
        self.name = name

    def get_axioms(self) -> list[FNode]:
        return TRUE()
