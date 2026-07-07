"""Constant propagation for memory-bus multiplicities (internal, uncertified).

TODO: once this mechanism has settled, promote extracted equalities to typed
facts (single-column pins vs multi-column linear zeros — names TBD) so certify
can justify propagated multiplicities.
"""
from __future__ import annotations

import json
from typing import TYPE_CHECKING, Any

from src.lens.normalize import BABYBEAR_PRIME, to_signed

from .busmodel import BITWISE, TUPLE_RANGE, VAR_RANGE, MemRow, range_bus_rows
from .facts import TS_MAX
from .linform import LinForm, domain_gadget, linform, product

if TYPE_CHECKING:
    from .rules import Analysis

P = BABYBEAR_PRIME

# (lo, hi_exclusive); hi None = unbounded above lo
_PropBound = tuple[int, int | None]


def _bits_of(arg: Any) -> int | None:
    if isinstance(arg, str) and arg.isdigit():
        arg = int(arg)
    return arg if isinstance(arg, int) and 0 <= arg < 31 else None


def prop_bounds(an: Analysis) -> dict[str, _PropBound]:
    """Bounds for propagation window checks — no dependency on ``kinds``."""
    out: dict[str, _PropBound] = {}

    def put(col: str, lo: int, hi: int | None) -> None:
        cur = out.get(col)
        if cur is None:
            out[col] = (lo, hi)
        elif hi is not None and (cur[1] is None or hi < cur[1]):
            out[col] = (lo, hi)

    for _idx, bid, args in range_bus_rows(an.machine):
        if bid == VAR_RANGE and len(args) >= 2:
            bits = _bits_of(args[1])
            if bits is None:
                continue
            val = args[0]
            if isinstance(val, str):
                put(val, 0, 1 << bits)
            elif (isinstance(val, list) and len(val) == 3 and val[1] == "*"
                  and isinstance(val[0], int) and isinstance(val[2], str)):
                try:
                    s = pow(val[0] % P, -1, P)
                except ValueError:
                    continue
                if s * (1 << bits) < P:
                    put(val[2], 0, s * (1 << bits))
        elif bid == BITWISE:
            for a in args[:2]:
                if isinstance(a, str):
                    put(a, 0, 1 << 8)
        elif bid == TUPLE_RANGE:
            for a in args:
                if isinstance(a, str):
                    put(a, 0, None)

    for con in an.machine.get("constraints", []):
        lf = linform(con)
        if lf is not None and len(lf.coeffs) == 1:
            put(lf.coeffs[0][0], 0, TS_MAX)
        dg = domain_gadget(con)
        if dg is not None:
            put(dg[0], 0, dg[1])
            continue
        pr = product(con)
        if pr is None:
            continue
        if (pr.left.coeffs == pr.right.coeffs
                and pr.right.const == pr.left.const - 1
                and len(pr.left.coeffs) == 1
                and pr.left.coeffs[0][1] == 1):
            put(pr.left.coeffs[0][0], 0, 2)

    for row in an.mem:
        if isinstance(row.addr_space_expr, str):
            put(row.addr_space_expr, 0, TS_MAX)
        if isinstance(row.ptr, str):
            put(row.ptr, 0, TS_MAX)
        for byte in row.data:
            if isinstance(byte, str):
                put(byte, 0, 1 << 8)
        if isinstance(row.ts, str):
            put(row.ts, 0, TS_MAX)

    return out


def _prop_window(lf: LinForm, bounds: dict[str, _PropBound]) -> tuple[int, int] | None:
    lo = hi = lf.const
    for col, c in lf.coeffs:
        b = bounds.get(col)
        if b is None or b[1] is None or b[0] < 0:
            return None
        top = b[1] - 1
        lo += min(0, c * top)
        hi += max(0, c * top)
    return lo, hi


def _window_sound(lo: int, hi: int) -> bool:
    return lo > -P and hi < P


def _try_pin(lf: LinForm, bounds: dict[str, _PropBound]) -> tuple[str, int] | None:
    """``lf ≡ 0`` with a single column ⟹ pin that column, if window-unique."""
    if len(lf.coeffs) != 1:
        return None
    win = _prop_window(lf, bounds)
    if win is None or not _window_sound(*win):
        return None
    col, coeff = lf.coeffs[0]
    if coeff == 1:
        return col, LinForm.make({}, -lf.const).const
    if coeff == -1:
        return col, LinForm.make({}, lf.const).const
    return None


def _neg_coeffs(coeffs: tuple[tuple[str, int], ...]) -> tuple[tuple[str, int], ...]:
    return tuple((c, -v) for c, v in coeffs)


def propagate(an: Analysis) -> tuple[dict[str, int], list[LinForm]]:
    """Fixpoint column pins + residual linear zeros (after substitution)."""
    bounds = prop_bounds(an)
    raw = [lf for c in an.machine.get("constraints", [])
           if (lf := linform(c)) is not None]
    pins: dict[str, int] = {}
    changed = True
    while changed:
        changed = False
        for lf_raw in raw:
            lf = lf_raw.subst(pins)
            if lf.is_const:
                continue
            hit = _try_pin(lf, bounds)
            if hit is not None and hit[0] not in pins:
                pins[hit[0]] = hit[1]
                changed = True

    zeros: list[LinForm] = []
    for lf_raw in raw:
        lf = lf_raw.subst(pins)
        if lf.is_const:
            continue
        win = _prop_window(lf, bounds)
        if win is not None and _window_sound(*win):
            zeros.append(lf)
    return pins, zeros


def eval_mult(mf: LinForm | None, pins: dict[str, int],
              zeros: list[LinForm]) -> int | None:
    """Evaluate a multiplicity linear form; ``None`` if not resolved."""
    if mf is None:
        return None
    mf = mf.subst(pins)
    if mf.is_const:
        return mf.const % P
    for lf in zeros:
        if mf.coeffs == lf.coeffs:
            return (mf.const - lf.const) % P
        if mf.coeffs == _neg_coeffs(lf.coeffs):
            return (mf.const + lf.const) % P
    return None


def _lf_to_expr(lf: LinForm) -> Any:
    if lf.is_const:
        return lf.const
    parts: list[Any] = []
    for col, c in lf.coeffs:
        if c == 1:
            parts.append(col)
        elif c == -1:
            parts.append(["-", col])
        else:
            parts.append([c, "*", col])
    if lf.const != 0:
        parts.append(lf.const)
    expr = parts[0]
    for p in parts[1:]:
        expr = [expr, "+", p]
    return expr


def simplify_expr(pins: dict[str, int], zeros: list[LinForm], expr: Any) -> Any:
    """Fold propagation into a dump expression; resolve to int when possible."""
    v = eval_expr(pins, zeros, expr)
    if v is not None:
        return v
    lf = linform(expr)
    if lf is None:
        return expr
    lf = lf.subst(pins)
    return lf.const if lf.is_const else _lf_to_expr(lf)


def simplify_mult(pins: dict[str, int], zeros: list[LinForm], mult: Any) -> Any:
    lf = linform(mult)
    if lf is None:
        return mult
    v = eval_mult(lf, pins, zeros)
    if v is not None:
        return to_signed(v)
    lf = lf.subst(pins)
    return lf.const if lf.is_const else _lf_to_expr(lf)


def simplify_mem_row(row: MemRow, pins: dict[str, int], zeros: list[LinForm]) -> MemRow:
    return MemRow(row.ordinal,
                  simplify_mult(pins, zeros, row.mult),
                  tuple(simplify_expr(pins, zeros, a) for a in row.args))


def eval_expr(pins: dict[str, int], zeros: list[LinForm], expr: Any) -> int | None:
    """Resolve a linear dump expression via propagation, or ``None``."""
    if isinstance(expr, int):
        return to_signed(expr)
    lf = linform(expr)
    if lf is None:
        return None
    v = eval_mult(lf, pins, zeros)
    return to_signed(v) if v is not None else None


def format_debug(an: Analysis) -> str:
    """Human-readable propagation state and simplified memory rows."""
    pins, zeros = an._propagation
    lines = [f"# propagation pins ({len(pins)})"]
    for col in sorted(pins):
        lines.append(f"  {col} = {pins[col]}")
    lines.append(f"# propagation zeros ({len(zeros)})")
    for lf in zeros:
        lines.append(f"  {lf}")
    lines.append(f"# memory interactions ({len(an.mem)}) after simplification")
    for r in an.mem:
        lines.append(
            f"  #{r.ordinal}  mult={json.dumps(r.mult)}  args={json.dumps(list(r.args))}")
    return "\n".join(lines)
