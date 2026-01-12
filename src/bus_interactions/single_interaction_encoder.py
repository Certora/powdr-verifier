from ..smt_utils import *

class SingleInteractionEncoder:
    def __init__(self, name: str):
        self.name = name

    def get_axioms(self) -> list[FNode]:
        return TRUE()
    
    def get_globals(self) -> frozenset[FNode]:
        return getattr(self, 'globals', frozenset())
