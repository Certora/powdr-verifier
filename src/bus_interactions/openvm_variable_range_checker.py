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

    # Widest row the checker is instantiated for; a larger `bits` is not a table
    # row, so it gets the widest bound we can justify.
    MAX_BITS = 25

    @none_if(lambda: ARGS().no_varrange)
    def encode_pointwise(self, mult: Any, x: Any, bits: Any) -> FNode:
        """Constrain `x` to be in [0, 2^bits) when the interaction is enabled."""
        # `x`, `mult` and `bits` are stored already reduced mod P (see
        # SingleInteractionEncoder._wrap_field), so plain relational operators
        # apply directly.
        if bits.is_int_constant():
            bound = LT(x, Int(2 ** min(bits.constant_value(), self.MAX_BITS)))
        else:
            # Symbolic width. The shift chips range-check `bit_shift_carry[i]`
            # against the *decoded* shift amount (`Σ k·bit_shift_marker__k`), so
            # collapsing this to the widest row (`x < 2^25`) throws almost all of
            # the fact away: for a shift by a multiple of 8 the true width is 0,
            # i.e. the carry is *zero*, and without that the shift's limb
            # relation stops pinning the output limbs -- which showed up as
            # spurious `solver` completeness counterexamples (reth 2099608 and
            # 2099872, where powdr substitutes `b__3_k := a__0_k` for an
            # srl-by-24). The width comes from a small finite set, so case-split
            # over it and keep the widest row as the fallback bound.
            bound = And(
                LT(x, Int(2**self.MAX_BITS)),
                *[
                    Implies(Equals(bits, Int(k)), LT(x, Int(2**k)))
                    for k in range(self.MAX_BITS)
                ],
            )

        if mult.is_int_constant() and mult.constant_value() != 0:
            fact = bound
        else:
            fact = Implies(Not(Equals(mult, Int(0))), bound)
        # The range is table semantics — the lookup table only contains
        # valid rows, so the circuit RELIES on `x < 2^bits`; it does not
        # establish it. As a constraint, each goal-side copy becomes a
        # `2^bits <= x` proof obligation over post-substitution expressions
        # (uf_xor-threaded on keccak) — practically unprovable. Grant it
        # through the axioms channel instead (cf. TS_BOUND, bitwise lift).
        if ARGS().varrange_axioms:
            self.consequences.append(
                with_comment(fact, f"{self.NAME} table semantics (granted)")
            )
            return TRUE()
        return fact
