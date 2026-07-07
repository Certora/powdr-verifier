"""Constant propagation for memory-bus multiplicities (internal, uncertified).

TODO: once this mechanism has settled, promote extracted equalities to typed
facts (single-column pins vs multi-column linear zeros — names TBD) so certify
can justify propagated multiplicities.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass
from itertools import product as iproduct
from typing import TYPE_CHECKING, Any

from src.lens.normalize import BABYBEAR_PRIME, to_signed

from .busmodel import BITWISE, TUPLE_RANGE, VAR_RANGE, MemRow, range_bus_rows
from .facts import TS_MAX
from .linform import LinForm, bits_of, domain_gadget, linform, names, product

if TYPE_CHECKING:
    from .rules import Analysis

P = BABYBEAR_PRIME

# (lo, hi_exclusive); hi None = unbounded above lo
_PropBound = tuple[int, int | None]


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
            bits = bits_of(args[1])
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


_IS_LOAD_RE = re.compile(r"^is_load_(\d+)@")
_ACCESS_RE = re.compile(r"_(\d+)@\d+$")


def _eval_constraint(expr: Any, env: dict[str, int]) -> int:
    """Evaluate a dump constraint expression mod p (uncertified).

    Missing columns default to 0 — only for constraint SAT over a partial env
    (e.g. flag enumeration). Use :func:`_eval_partial` when unbound columns
    must not be guessed.
    """
    if isinstance(expr, bool):
        raise ValueError(f"unexpected bool: {expr!r}")
    if isinstance(expr, int):
        return expr % P
    if isinstance(expr, str):
        return env.get(expr, 0) % P
    if isinstance(expr, list) and len(expr) == 2 and expr[0] == "-":
        return (-_eval_constraint(expr[1], env)) % P
    if isinstance(expr, list) and len(expr) == 3:
        a, op, b = expr
        av, bv = _eval_constraint(a, env), _eval_constraint(b, env)
        if op == "+":
            return (av + bv) % P
        if op == "-":
            return (av - bv) % P
        if op == "*":
            return (av * bv) % P
    raise ValueError(f"cannot eval: {expr!r}")


def _eval_partial(expr: Any, env: dict[str, int]) -> int | None:
    """Evaluate mod p, or ``None`` if a remaining column is not in ``env``.

    ``0 * <unbound>`` and ``<unbound> * 0`` fold to 0 without reading the
    unbound factor (pinned zeros can eliminate a column from the value).
    """
    if isinstance(expr, bool):
        raise ValueError(f"unexpected bool: {expr!r}")
    if isinstance(expr, int):
        return expr % P
    if isinstance(expr, str):
        if expr not in env:
            return None
        return env[expr] % P
    if isinstance(expr, list) and len(expr) == 2 and expr[0] == "-":
        v = _eval_partial(expr[1], env)
        return None if v is None else (-v) % P
    if isinstance(expr, list) and len(expr) == 3:
        a, op, b = expr
        if op == "*":
            av = _eval_partial(a, env)
            bv = _eval_partial(b, env)
            if av == 0 or bv == 0:
                return 0
            if av is None or bv is None:
                return None
            return (av * bv) % P
        av = _eval_partial(a, env)
        bv = _eval_partial(b, env)
        if av is None or bv is None:
            return None
        if op == "+":
            return (av + bv) % P
        if op == "-":
            return (av - bv) % P
    raise ValueError(f"cannot eval: {expr!r}")


def _all_constraint_cols(machine: dict) -> set[str]:
    out: set[str] = set()
    for c in machine.get("constraints", []):
        out |= names(c)
    return out


def _flag_cols_for_access(cols: set[str], access: int) -> tuple[str, ...]:
    needle = f"_{access}@"
    return tuple(sorted(c for c in cols if c.startswith("flags__") and needle in c))


@dataclass(frozen=True)
class _DecodingIndex:
    """Pre-indexed mux / flag-domain constraints for is_load refutation."""

    mux_by_is_load: dict[str, Any]
    nonlinear_by_names: dict[frozenset[str], tuple[Any, ...]]

    @classmethod
    def build(cls, cons: list[Any]) -> _DecodingIndex:
        mux: dict[str, Any] = {}
        nonlinear: dict[frozenset[str], list[Any]] = {}
        for c in cons:
            if (isinstance(c, list) and len(c) == 3 and c[1] == "-"
                    and isinstance(c[0], str) and c[0] not in mux):
                mux[c[0]] = c
            if linform(c) is None:
                nonlinear.setdefault(frozenset(names(c)), []).append(c)
        return cls(mux, {k: tuple(v) for k, v in nonlinear.items()})

    def flag_domain_nonlinear(self, flag_cols: tuple[str, ...],
                              is_load: str) -> list[Any]:
        candidates = self.nonlinear_by_names.get(frozenset(flag_cols), ())
        return [c for c in candidates if is_load not in names(c)]

    def deciding_constraints(self, is_load: str,
                             flag_cols: tuple[str, ...]) -> list[Any]:
        out: list[Any] = []
        mux = self.mux_by_is_load.get(is_load)
        if mux is not None:
            out.append(mux)
        out.extend(self.flag_domain_nonlinear(flag_cols, is_load))
        return out


def _flag_domain_nonlinear(cons: list[Any], flag_cols: tuple[str, ...],
                           is_load: str) -> list[Any]:
    """Nonlinear constraints mentioning only this access's decode flags."""
    need = set(flag_cols)
    return [c for c in cons
            if linform(c) is None and is_load not in names(c)
            and names(c) == need]


def _mux_constraint(cons: list[Any], is_load: str) -> Any | None:
    for c in cons:
        if (isinstance(c, list) and len(c) == 3 and c[1] == "-"
                and c[0] == is_load):
            return c
    return None


def _deciding_constraints(cons: list[Any], is_load: str, flag_cols: tuple[str, ...],
                          pins: dict[str, int],
                          index: _DecodingIndex | None = None) -> list[Any]:
    """Mux + flag-domain nonlinear constraints for this access."""
    del pins  # env supplies Step-1 pins; no extra linear bundle needed
    if index is not None:
        return index.deciding_constraints(is_load, flag_cols)
    out: list[Any] = []
    mux = _mux_constraint(cons, is_load)
    if mux is not None:
        out.append(mux)
    out.extend(_flag_domain_nonlinear(cons, flag_cols, is_load))
    return out


def _sat_with_flags(cons: list[Any], env: dict[str, int],
                    flag_cols: tuple[str, ...]) -> bool:
    for bits in iproduct((0, 1), repeat=len(flag_cols)):
        trial = dict(env)
        for col, v in zip(flag_cols, bits):
            trial[col] = v
        if all(_eval_constraint(c, trial) == 0 for c in cons):
            return True
    return False


def _refute_is_load(is_load: str, flag_cols: tuple[str, ...],
                    index: _DecodingIndex, pins: dict[str, int]) -> int | None:
    deciding = index.deciding_constraints(is_load, flag_cols)
    if not deciding:
        return None
    survivors: list[int] = []
    for v in (0, 1):
        if _sat_with_flags(deciding, {**pins, is_load: v}, flag_cols):
            survivors.append(v)
    return survivors[0] if len(survivors) == 1 else None


def _refute_is_load_pins(an: Analysis, pins: dict[str, int],
                         index: _DecodingIndex) -> dict[str, int]:
    cols = _all_constraint_cols(an.machine)
    out = dict(pins)
    for is_load in sorted(c for c in cols if c.startswith("is_load_")):
        if is_load in out:
            continue
        m = _IS_LOAD_RE.match(is_load)
        if m is None:
            continue
        flag_cols = _flag_cols_for_access(cols, int(m.group(1)))
        if not flag_cols:
            continue
        v = _refute_is_load(is_load, flag_cols, index, out)
        if v is not None:
            out[is_load] = v
    return out


def _accesses_in_expr(expr: Any) -> set[int]:
    out: set[int] = set()
    for col in names(expr):
        m = _ACCESS_RE.search(col)
        if m is not None:
            out.add(int(m.group(1)))
    return out


def surviving_envs(an: Analysis, pins: dict[str, int],
                   index: _DecodingIndex) -> dict[int, list[dict[str, int]]]:
    """Pinned + flag assignments satisfying each access's mux/opcode cone."""
    cols = _all_constraint_cols(an.machine)
    out: dict[int, list[dict[str, int]]] = {}
    for is_load in sorted(c for c in cols if c.startswith("is_load_")):
        m = _IS_LOAD_RE.match(is_load)
        if m is None or is_load not in pins:
            continue
        access = int(m.group(1))
        flag_cols = _flag_cols_for_access(cols, access)
        if not flag_cols:
            continue
        deciding = index.deciding_constraints(is_load, flag_cols)
        envs: list[dict[str, int]] = []
        for bits in iproduct((0, 1), repeat=len(flag_cols)):
            trial = {**pins, is_load: pins[is_load]}
            for col, v in zip(flag_cols, bits):
                trial[col] = v
            if all(_eval_constraint(c, trial) == 0 for c in deciding):
                envs.append(trial)
        if envs:
            out[access] = envs
    return out


def _refute_expr(expr: Any, pins: dict[str, int],
                 envs_by_access: dict[int, list[dict[str, int]]]) -> int | None:
    """If ``expr`` has one value under every surviving flag env, return it.

    Pin-fold first, then evaluate with :func:`_eval_partial` so columns
    eliminated by pinned zeros (e.g. ``is_load * rd`` with ``is_load=0``) do
    not block folding; unbound columns that still affect the value yield
    ``None`` rather than defaulting to 0.
    """
    if isinstance(expr, int):
        return to_signed(expr)
    accs = _accesses_in_expr(expr)
    if len(accs) != 1:
        return None
    envs = envs_by_access.get(next(iter(accs)))
    if not envs:
        return None
    folded = _fold_pins(expr, pins)
    if isinstance(folded, int):
        return folded
    vals: set[int] = set()
    for env in envs:
        v = _eval_partial(folded, env)
        if v is None:
            return None
        vals.add(to_signed(v))
    return next(iter(vals)) if len(vals) == 1 else None


def propagate(an: Analysis) -> tuple[dict[str, int], list[LinForm], _DecodingIndex]:
    """Fixpoint column pins + residual linear zeros (after substitution)."""
    bounds = prop_bounds(an)
    cons = an.machine.get("constraints", [])
    decoding = _DecodingIndex.build(cons)
    raw = [lf for c in cons if (lf := linform(c)) is not None]
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

    pins = _refute_is_load_pins(an, pins, decoding)

    zeros: list[LinForm] = []
    for lf_raw in raw:
        lf = lf_raw.subst(pins)
        if lf.is_const:
            continue
        win = _prop_window(lf, bounds)
        if win is not None and _window_sound(*win):
            zeros.append(lf)
    return pins, zeros, decoding


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


def _fold_pins(expr: Any, pins: dict[str, int]) -> Any:
    """Substitute pinned columns; evaluate mod-p when no columns remain."""
    if isinstance(expr, int):
        return expr
    if isinstance(expr, str):
        return pins.get(expr, expr)
    if isinstance(expr, list) and len(expr) == 2 and expr[0] == "-":
        inner = _fold_pins(expr[1], pins)
        if isinstance(inner, int):
            return to_signed(-inner)
        return ["-", inner]
    if isinstance(expr, list) and len(expr) == 3:
        a = _fold_pins(expr[0], pins)
        b = _fold_pins(expr[2], pins)
        op = expr[1]
        if isinstance(a, int) and isinstance(b, int):
            if op == "+":
                return to_signed(a + b)
            if op == "-":
                return to_signed(a - b)
            if op == "*":
                return to_signed(a * b)
        if op == "*":
            if a == 0 or b == 0:
                return 0
            if a == 1:
                return b
            if b == 1:
                return a
        if op == "+":
            if a == 0:
                return b
            if b == 0:
                return a
        if op == "-":
            if b == 0:
                return a
            if a == 0:
                if isinstance(b, int):
                    return to_signed(-b)
                return ["-", b]
        return [a, op, b]
    return expr


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
    folded = _fold_pins(expr, pins)
    if isinstance(folded, int):
        return folded
    if folded is not expr:
        v = eval_expr(pins, zeros, folded)
        if v is not None:
            return v
        expr = folded
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


def simplify_mem_row(row: MemRow, pins: dict[str, int], zeros: list[LinForm],
                   envs_by_access: dict[int, list[dict[str, int]]]) -> MemRow:
    as_arg = simplify_expr(pins, zeros, row.args[0])
    ptr_arg = _refute_expr(row.args[1], pins, envs_by_access)
    if ptr_arg is None:
        ptr_arg = simplify_expr(pins, zeros, row.args[1])
    ts_arg = simplify_expr(pins, zeros, row.args[-1])
    args = (as_arg, ptr_arg, *row.args[2:-1], ts_arg)
    return MemRow(row.ordinal, simplify_mult(pins, zeros, row.mult), args)


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
