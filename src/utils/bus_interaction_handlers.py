from enum import Enum

class BusInteractionHandlers(Enum):
    OPENVM = 'openvm'
    DEFAULT = OPENVM

    def __str__(self) -> str:
        return self.value
