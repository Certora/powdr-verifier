from enum import Enum

class FieldTypes(Enum):
    """An enum of all field types we support."""
    BABYBEAR = 0x78000001
    KOALABEAR = 0x7f000001
    GOLDILOCKS = 0xFFFFFFFF00000001

    def __str__(self) -> str:
        return self.name.lower()
