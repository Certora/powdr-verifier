"""Bitwise lookup bus: truth table via uninterpreted ``UF_XOR`` and multiplicity axioms."""
import logging
from typing import Any, Optional

from .single_interaction_encoder import SingleInteractionEncoder

from ..smt.utils import *
from ..utils.enums import XOrEncoding
from ..utils.utils import none_if


def _trim_mod_p(p: int, terms: dict) -> dict:
    out: dict = {}
    for sym, c in terms.items():
        c %= p
        if c != 0:
            out[sym] = c
    return out


def _linear_z_minus_x_minus_y(
    p: int,
    tx: dict,
    cx: int,
    ty: dict,
    cy: int,
    tz: dict,
    cz: int,
) -> tuple[dict, int]:
    terms: dict = {}
    for t, mul in ((tz, 1), (tx, -1), (ty, -1)):
        for s, c in t.items():
            terms[s] = terms.get(s, 0) + mul * c
    return _trim_mod_p(p, terms), (cz - cx - cy) % p


def _linear_z_plus_x_plus_y(
    p: int,
    tx: dict,
    cx: int,
    ty: dict,
    cy: int,
    tz: dict,
    cz: int,
) -> tuple[dict, int]:
    terms: dict = {}
    for t, mul in ((tz, 1), (tx, 1), (ty, 1)):
        for s, c in t.items():
            terms[s] = terms.get(s, 0) + mul * c
    return _trim_mod_p(p, terms), (cz + cx + cy) % p


class OpenVMBitwiseLookupEncoder(SingleInteractionEncoder):
    """
    Encodes bitwise lookup bus interactions. It implements two cases:

    * `(x, y, 0, 0)` constrains `x` and `y` to be bytes
    * `(x, y, z, 1)` constrains `x`, `y`, and `z` to be bytes and `z = x xor y`

    The xor is encoded as an overapproximating `uf_xor` that is restricted
    on a best-effort basis by some axioms.
    """

    UF_XOR = Symbol("uf_xor", FunctionType(INT, [INT, INT]))
    UF_AND = Symbol("uf_and", FunctionType(INT, [INT, INT]))
    UF_OR = Symbol("uf_or", FunctionType(INT, [INT, INT]))
    WRAP_XOR = lambda self, x, y: Ite(
        Equals(x, Int(0)), y,
        Ite(
            Equals(y, Int(0)), x,
            Ite(Equals(x, y), Int(0),
            Function(self.UF_XOR, [x, y]))
        )
    )
    interpreters = {
        UF_XOR: (
            lambda x, y: Int(x ^ y),
            lambda x, y: (
                y
                if x.is_zero()
                else (x if y.is_zero() else (Int(0) if x == y else None))
            ),
        ),
        UF_AND: (
            lambda x, y: Int(x & y),
            lambda x, y: (
                Int(0)
                if x.is_zero() or y.is_zero()
                else (x if x == y else None)
            ),
        ),
        UF_OR: (
            lambda x, y: Int(x | y),
            lambda x, y: (
                y if x.is_zero() else (x if y.is_zero() or x == y else None)
            ),
        ),
    }
    NAME = "bitwise lookup"

    def __init__(self) -> None:
        """Initialize the encoder and mark bitwise lookup UFs as global symbols."""
        super().__init__()
        self.globals = frozenset([self.UF_XOR, self.UF_AND, self.UF_OR])
    
    def __XOR(self, x: Any, y: Any) -> FNode:
        match ARGS().xor:
            case (
                XOrEncoding.GROUNDED
                | XOrEncoding.AXIOMS
            ):
                return Function(self.UF_XOR, [x, y])
            case XOrEncoding.WRAPPED_AXIOMS:
                return self.WRAP_XOR(x, y)
            case XOrEncoding.WRAPPED_GROUNDED:
                return self.WRAP_XOR(x, y)
            case _:
                raise ValueError(f"Unsupported XOR encoding: {ARGS().xor}")

    def _and_or_target(self, x: Any, y: Any, z: Any) -> Optional[tuple[FNode, str]]:
        """Column computed as ``AND(x, y)`` / ``OR(x, y)`` through the XOR table.

        OpenVM encodes bitwise AND/OR by sending ``z = x + y - 2a`` (then
        ``a = x AND y``) or ``z = 2a - x - y`` (then ``a = x OR y``) as the
        XOR argument: by ``x + y = (x XOR y) + 2 (x AND y)`` the table pins
        ``a`` to a byte. The SMT side loses this — ``uf_xor``
        over-approximates the table and drops the evenness of
        ``x + y - z``, so the byte range on ``a`` is chip semantics that
        must be restored explicitly, not derived.

        Matching is purely on linear forms of ``x``, ``y``, ``z``. Plain XOR
        rows with ``x`` and ``y`` the same term (``x ⊕ x = 0``) satisfy
        ``z - x - y = -2x`` spuriously, so those are skipped.

        Returns ``(column, "and" | "or")`` or ``None``.
        """
        if x == y:
            return None
        p = ARGS().field_type.value
        forms = [linear_form(e) for e in (x, y, z)]
        if any(f is None for f in forms):
            return None
        (tx, cx), (ty, cy), (tz, cz) = forms
        terms, const = _linear_z_minus_x_minus_y(p, tx, cx, ty, cy, tz, cz)
        if const == 0 and len(terms) == 1:
            a, c = next(iter(terms.items()))
            if c == (-2) % p:
                return a, "and"
        terms, const = _linear_z_plus_x_plus_y(p, tx, cx, ty, cy, tz, cz)
        if const == 0 and len(terms) == 1:
            a, c = next(iter(terms.items()))
            if c == 2 % p:
                return a, "or"
        return None

    @none_if(lambda: ARGS().no_bitwise)
    def encode_pointwise(self, mult: Any, x: Any, y: Any, z: Any, op: Any) -> Optional[FNode]:
        """Encode byte-range constraints and XOR relation depending on `op`."""
        if op == Int(0) and z == Int(0):
            return Implies(
                Not(Equals(wrap_mod(mult), Int(0))),
                And(
                    LE(Int(0), wrap_mod(x)),
                    LE(wrap_mod(x), Int(255)),
                    LE(Int(0), wrap_mod(y)),
                    LE(wrap_mod(y), Int(255)),
                    Equals(z, Int(0)),
                    Equals(op, Int(0)),
                ),
            )
        elif op == Int(1):
            facts = [
                LE(Int(0), wrap_mod(x)),
                LE(wrap_mod(x), Int(255)),
                LE(Int(0), wrap_mod(y)),
                LE(wrap_mod(y), Int(255)),
                LE(Int(0), wrap_mod(z)),
                LE(wrap_mod(z), Int(255)),
                Equals(self.__XOR(wrap_mod(x), wrap_mod(y)), wrap_mod(z)),
                Equals(op, Int(1)),
            ]
            target = self._and_or_target(x, y, z)
            if target is not None:
                a, kind = target
                wx, wy = wrap_mod(x), wrap_mod(y)
                fn = self.UF_AND if kind == "and" else self.UF_OR
                conj = Function(self.UF_AND, [wx, wy])
                lift = [
                    with_comment(
                        Equals(a, Function(fn, [wx, wy])),
                        f"BITWISE lift: {a} = {kind}({x}, {y})",
                    ),
                    # ground axioms for the uf_and application; the
                    # linking x + y = xor + 2 and carries the evenness
                    # the bare table encoding loses
                    LE(Int(0), conj),
                    LE(conj, wx),
                    LE(conj, wy),
                    Equals(
                        Plus(wx, wy),
                        Plus(self.__XOR(wx, wy), Times(Int(2), conj)),
                    ),
                    # byte range on the result (table semantics; for OR it
                    # is not a linear consequence of the bounds above)
                    And(LE(Int(0), a), LE(a, Int(255))),
                ]
                if ARGS().bitwise_lift_axioms:
                    # The lift is table/chip semantics — a granted
                    # environment fact, not a circuit commitment. Route it
                    # through the axioms channel (premise for BOTH sides,
                    # never a proof obligation); as a constraint, each
                    # goal-side copy becomes an `xor = x+y-2and` obligation
                    # over uf terms that solve-eqs/demod rewrite apart —
                    # practically unprovable (cf. TS_BOUND, PR #40).
                    self.axioms.append(
                        with_comment(
                            Implies(
                                Not(Equals(wrap_mod(mult), Int(0))),
                                And(*lift),
                            ),
                            f"{self.NAME} lift for {a} (granted)",
                        )
                    )
                else:
                    facts += lift
            return Implies(
                Not(Equals(wrap_mod(mult), Int(0))),
                And(*facts),
            )
        else:
            logging.error(f"Unsupported bitwise operation: {op}")
            return None
