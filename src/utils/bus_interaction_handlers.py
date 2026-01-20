from enum import Enum

class BusInteractionHandlers(Enum):
    """An enum of all bus interaction handlers we support."""
    OPENVM = 'openvm'
    DEFAULT = OPENVM

    def __str__(self) -> str:
        return self.value
