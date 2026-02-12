from enum import Enum


class FieldTypes(Enum):
    """An enum of all field types we support."""

    BABYBEAR = 0x78000001
    KOALABEAR = 0x7F000001
    GOLDILOCKS = 0xFFFFFFFF00000001

    def __str__(self) -> str:
        """Return the string representation for this field type."""
        return self.name.lower()
