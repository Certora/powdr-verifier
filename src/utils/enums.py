"""Enumerations for bus backends, field modulus, and XOR encoding strategy."""
from enum import Enum
from pickle import DEFAULT_PROTOCOL


class BusInteractionHandlers(Enum):
    """An enum of all bus interaction handlers we support."""

    OPENVM = "openvm"
    DEFAULT = OPENVM

    def __str__(self) -> str:
        """Return the string representation for this enum value."""
        return self.value


class FieldTypes(Enum):
    """An enum of all field types we support."""

    BABYBEAR = 0x78000001
    KOALABEAR = 0x7F000001
    GOLDILOCKS = 0xFFFFFFFF00000001

    def __str__(self) -> str:
        """Return the string representation for this field type."""
        return self.name.lower()


class XOrEncoding(Enum):
    """An enum of all XOR encodings we support."""

    AXIOMS = "axioms"
    GROUNDED = "grounded"
    WRAPPED_AXIOMS = "wrapped-axioms"
    WRAPPED_GROUNDED = "wrapped-grounded"
    DEFAULT = AXIOMS

    def __str__(self) -> str:
        """Return the string representation for this XOR encoding."""
        return self.value