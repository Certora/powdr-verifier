"""Recognizer for AND/OR-encoded XOR-table rows (`_and_or_target`).

Regression for guest-keccak 2105476 002->003: an AND row whose operand
carried an un-normalized coefficient ``(1-1)*a`` was recognized on its folded
side (post ``solver`` pass) but missed on its unfolded side, leaving that side
without the AND byte-range axioms -> spurious ``sat``. The recognizer now
normalizes its arguments first, so recognition no longer depends on whether an
upstream pass folded the coefficients.
"""
from src.bus_interactions.openvm_bitwise_lookup import OpenVMBitwiseLookupEncoder
from src.smt.utils import *
from src.utils.args import parse_args


def _enc():
    parse_args(["verify", "x", "y", "z"])  # initialize ARGS().field_type
    return OpenVMBitwiseLookupEncoder()


def test_recognizes_folded_and_row():
    """a = x AND y is sent as z = x + y - 2a; folded form is recognized."""
    enc = _enc()
    a, b, c = (Symbol(n, INT) for n in ("a__0_0", "b__0_0", "c__0_0"))
    x, y = b, c
    z = Minus(Plus(b, c), Times(Int(2), a))
    assert enc._and_or_target(x, y, z) == (a, "and")


def test_recognizes_unfolded_and_row():
    """Same AND row with an un-normalized ``(1-1)*a`` coefficient on x: without
    normalization `linear_form` bails and the row is missed. The fix normalizes
    first, so it is recognized identically to the folded form."""
    enc = _enc()
    a, b, c = (Symbol(n, INT) for n in ("a__0_0", "b__0_0", "c__0_0"))
    x = Plus(Times(Minus(Int(1), Int(1)), a), b)  # (1-1)*a + b  ==  b
    y = c
    z = Minus(Plus(b, c), Times(Int(2), a))
    assert enc._and_or_target(x, y, z) == (a, "and")


def test_recognizes_or_row():
    """a = x OR y is sent as z = 2a - x - y."""
    enc = _enc()
    a, b, c = (Symbol(n, INT) for n in ("a__0_0", "b__0_0", "c__0_0"))
    x, y = b, c
    z = Minus(Times(Int(2), a), Plus(b, c))
    assert enc._and_or_target(x, y, z) == (a, "or")


def test_plain_xor_row_is_not_matched():
    """A genuine XOR row (z is a fresh column, not x+y-2a) must not be lifted."""
    enc = _enc()
    a, b, c = (Symbol(n, INT) for n in ("a__0_0", "b__0_0", "c__0_0"))
    assert enc._and_or_target(b, c, a) is None


def test_equal_operands_not_matched_even_unfolded():
    """x ⊕ x = 0 spuriously satisfies z - x - y = -2x; must be skipped, including
    when one side is written un-normalized but is semantically equal to x."""
    enc = _enc()
    a, x = Symbol("a__0_0", INT), Symbol("x__0_0", INT)
    # y == x semantically but written (1-1)*a + x
    y = Plus(Times(Minus(Int(1), Int(1)), a), x)
    z = Int(0)
    assert enc._and_or_target(x, y, z) is None
