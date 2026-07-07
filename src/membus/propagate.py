"""Constant propagation for memory-bus multiplicities (internal, uncertified).

TODO: once this mechanism has settled, promote extracted equalities to typed
facts (single-column pins vs multi-column linear zeros — names TBD) so certify
can justify propagated multiplicities.
"""
from __future__ import annotations

import json
import re
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
    """Evaluate a dump constraint expression mod p (uncertified)."""
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


def _all_constraint_cols(machine: dict) -> set[str]:
    out: set[str] = set()
    for c in machine.get("constraints", []):
        out |= names(c)
    return out


def _flag_cols_for_access(cols: set[str], access: int) -> tuple[str, ...]:
    needle = f"_{access}@"
    return tuple(sorted(c for c in cols if c.startswith("flags__") and needle in c))


def _opcode_constraint(cons: list[Any], flag_cols: tuple[str, ...],
                       is_load: str) -> Any | None:
    """Nonlinear opcode decode: large literal + mux(flags) (+/- instruction word)."""
    need = set(flag_cols)
    for c in cons:
        if linform(c) is not None:
            continue
        n = names(c)
        if is_load in n or not need.issubset(n):
            continue
        blob = json.dumps(c)
        if any(f'"{v}"' in blob or str(v) in blob
               for v in (528, 529, 533, 534)):
            return c
    return None


def _mux_constraint(cons: list[Any], is_load: str) -> Any | None:
    for c in cons:
        if (isinstance(c, list) and len(c) == 3 and c[1] == "-"
                and c[0] == is_load):
            return c
    return None


def _deciding_constraints(cons: list[Any], is_load: str, flag_cols: tuple[str, ...],
                          pins: dict[str, int]) -> list[Any]:
    """Mux + opcode for this access; pins are already in the trial env."""
    del pins  # env supplies Step-1 pins; no extra linear bundle needed
    out: list[Any] = []
    mux = _mux_constraint(cons, is_load)
    if mux is not None:
        out.append(mux)
    opc = _opcode_constraint(cons, flag_cols, is_load)
    if opc is not None:
        out.append(opc)
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


def _refute_is_load(is_load: str, flag_cols: tuple[str, ...], cons: list[Any],
                    pins: dict[str, int]) -> int | None:
    deciding = _deciding_constraints(cons, is_load, flag_cols, pins)
    if not deciding:
        return None
    survivors: list[int] = []
    for v in (0, 1):
        if _sat_with_flags(deciding, {**pins, is_load: v}, flag_cols):
            survivors.append(v)
    return survivors[0] if len(survivors) == 1 else None


def _refute_is_load_pins(an: Analysis, pins: dict[str, int]) -> dict[str, int]:
    cols = _all_constraint_cols(an.machine)
    cons = an.machine.get("constraints", [])
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
        v = _refute_is_load(is_load, flag_cols, cons, out)
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


def surviving_envs(an: Analysis, pins: dict[str, int]) -> dict[int, list[dict[str, int]]]:
    """Pinned + flag assignments satisfying each access's mux/opcode cone."""
    cols = _all_constraint_cols(an.machine)
    cons = an.machine.get("constraints", [])
    out: dict[int, list[dict[str, int]]] = {}
    for is_load in sorted(c for c in cols if c.startswith("is_load_")):
        m = _IS_LOAD_RE.match(is_load)
        if m is None or is_load not in pins:
            continue
        access = int(m.group(1))
        flag_cols = _flag_cols_for_access(cols, access)
        if not flag_cols:
            continue
        deciding = _deciding_constraints(cons, is_load, flag_cols, pins)
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
    """If ``expr`` has one value under every surviving flag env, return it."""
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
        try:
            vals.add(to_signed(_eval_constraint(folded, env)))
        except ValueError:
            return None
    return next(iter(vals)) if len(vals) == 1 else None


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

    pins = _refute_is_load_pins(an, pins)

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
        if isinstance(a, int) and isinstance(b, int):
            if expr[1] == "+":
                return to_signed(a + b)
            if expr[1] == "-":
                return to_signed(a - b)
            if expr[1] == "*":
                return to_signed(a * b)
        return [a, expr[1], b]
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


def simplify_expr(pins: dict[str, int], zeros: list[LinForm], expr: Any,
                  *, envs_by_access: dict[int, list[dict[str, int]]] | None = None) -> Any:
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
                   envs_by_access: dict[int, list[dict[str, int]]] | None = None) -> MemRow:
    args: list[Any] = []
    for i, a in enumerate(row.args):
        if i == 1 and envs_by_access is not None:
            v = _refute_expr(a, pins, envs_by_access)
            args.append(v if v is not None
                        else simplify_expr(pins, zeros, a, envs_by_access=envs_by_access))
        else:
            args.append(simplify_expr(pins, zeros, a, envs_by_access=envs_by_access))
    return MemRow(row.ordinal, simplify_mult(pins, zeros, row.mult), tuple(args))


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
