"""Single-variable range checker: constrain ``x < 2**bits`` for small bit widths."""
from typing import Any

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *
from ..utils.utils import none_if


class OpenVMVariableRangeCheckerEncoder(SingleInteractionEncoder):
    """
    Encodes variable range checker bus interactions. It constrains the value to
    be below `2^bits`, and we generally assume `bits <= 25`.
    """

    NAME = "variable range checker"

    def __init__(self) -> None:
        super().__init__()
        self._granted: list[FNode] = []  # filled by encode_pointwise

    @none_if(lambda: ARGS().no_varrange)
    def encode_pointwise(self, mult: Any, x: Any, bits: Any) -> FNode:
        """Constrain `x` to be in [0, 2^bits) when the interaction is enabled."""
        curbits = 25
        if bits.is_int_constant() and bits.constant_value() <= 25:
            curbits = bits.constant_value()

        # `x` and `mult` are stored already reduced mod P (see
        # SingleInteractionEncoder._wrap_field), so plain relational operators
        # apply directly.
        if mult.is_int_constant() and mult.constant_value() != 0:
            fact = LT(x, Int(2**curbits))
        else:
            fact = Implies(
                Not(Equals(mult, Int(0))),
                LT(x, Int(2**curbits)),
            )
        # The range is table semantics — the lookup table only contains
        # valid rows, so the circuit RELIES on `x < 2^bits`; it does not
        # establish it. As a constraint, each goal-side copy becomes a
        # `2^bits <= x` proof obligation over post-substitution expressions
        # (uf_xor-threaded on keccak) — practically unprovable. Grant it
        # through the axioms channel instead (cf. TS_BOUND, bitwise lift).
        if ARGS().varrange_axioms:
            self._granted.append(
                with_comment(fact, f"{self.NAME} table semantics (granted)")
            )
            return TRUE()
        return fact

    def get_axioms(self) -> Iterable[FNode]:
        """Granted range-table assumptions (populated by `encode_pointwise`)."""
        yield from self._granted
