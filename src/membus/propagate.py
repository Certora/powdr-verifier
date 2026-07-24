"""Constant propagation for memory-bus multiplicities — certified via typed facts."""
from __future__ import annotations

import collections
import functools
import json
import re
from dataclasses import dataclass
from itertools import product as iproduct
from typing import TYPE_CHECKING, Any

from src.lens.normalize import BABYBEAR_PRIME, to_signed

from .busmodel import MemRow
from .facts import Bound, ExprEval, Fact, LinZero, Pin, Src
from .linform import LinForm, linform, names

if TYPE_CHECKING:
    from .rules import Analysis

P = BABYBEAR_PRIME

# Cap on the flag-assignment enumeration (product of per-flag domain sizes).
# Real opcode-flag groups are a handful of boolean/ternary columns; a wider
# product means a range-checked non-flag column slipped in, so decline instead
# of enumerating it.
_MAX_FLAG_ENUM = 1 << 16

_IS_LOAD_RE = re.compile(r"^is_load_(\d+)@")
_ACCESS_RE = re.compile(r"_(\d+)@\d+$")


def _certifiable(b: Bound) -> bool:
    return bool(b.sources) or bool(b.assumptions)


def _window_premises(lf: LinForm, bounds: dict[str, Bound],
                     ) -> tuple[int, int, tuple[Bound, ...]] | None:
    lo = hi = lf.const
    prem: list[Bound] = []
    for col, c in lf.coeffs:
        b = bounds.get(col)
        if b is None or b.hi is None or b.lo < 0:
            return None
        if not _certifiable(b):
            return None
        top = b.hi - 1
        prem.append(b)
        lo += min(0, c * top)
        hi += max(0, c * top)
    return lo, hi, tuple(prem)


def _window_sound(lo: int, hi: int) -> bool:
    return lo > -P and hi < P


def _try_pin(lf: LinForm, bounds: dict[str, Bound],
             ) -> tuple[str, int, tuple[Bound, ...]] | None:
    """``lf ≡ 0`` with a single column ⟹ pin that column, if window-unique."""
    if len(lf.coeffs) != 1:
        return None
    win = _window_premises(lf, bounds)
    if win is None or not _window_sound(win[0], win[1]):
        return None
    col, coeff = lf.coeffs[0]
    if coeff == 1:
        return col, LinForm.make({}, -lf.const).const, win[2]
    if coeff == -1:
        return col, LinForm.make({}, lf.const).const, win[2]
    return None


def _neg_coeffs(coeffs: tuple[tuple[str, int], ...]) -> tuple[tuple[str, int], ...]:
    return tuple((c, -v) for c, v in coeffs)


@dataclass(frozen=True)
class _DecodingIndex:
    """Pre-indexed mux / flag-domain constraints for is_load refutation."""

    mux_by_is_load: dict[str, tuple[int, Any]]
    nonlinear_by_names: dict[frozenset[str], tuple[tuple[int, Any], ...]]

    @classmethod
    def build(cls, cons: list[Any]) -> _DecodingIndex:
        mux: dict[str, tuple[int, Any]] = {}
        nonlinear: dict[frozenset[str], list[tuple[int, Any]]] = {}
        # Pass 1: forward decodes (is_load - g / g + is_load) take precedence.
        for idx, c in enumerate(cons):
            if isinstance(c, list) and len(c) == 3:
                if c[1] == "-" and isinstance(c[0], str):
                    mux.setdefault(c[0], (idx, c))
                elif c[1] == "+" and isinstance(c[2], str):
                    mux.setdefault(c[2], (idx, c))
            if linform(c) is None:
                nonlinear.setdefault(frozenset(names(c)), []).append((idx, c))
        # Pass 2: a reversed decode `g - is_load` is registered only if no forward
        # decode already claimed is_load — otherwise an alias like `freevar -
        # is_load` appearing first would shadow the genuine forward mux.
        # _refute_is_load solves the (-1) coefficient off the reversed mux.
        for idx, c in enumerate(cons):
            if (isinstance(c, list) and len(c) == 3
                    and c[1] == "-" and isinstance(c[2], str)):
                mux.setdefault(c[2], (idx, c))
        return cls(mux, {k: tuple(v) for k, v in nonlinear.items()})

    def flag_domain_nonlinear(self, flag_cols: tuple[str, ...],
                              is_load: str | None) -> list[tuple[int, Any]]:
        # Only gadgets whose column set is EXACTLY flag_cols qualify, so for a
        # multi-flag access the individual per-flag domain gadgets are omitted.
        # That only under-constrains the query (conservative — it can make a
        # spurious unsat impossible, never a spurious pass). is_load=None keeps
        # every gadget (used when no is_load pin exists for the access).
        candidates = self.nonlinear_by_names.get(frozenset(flag_cols), ())
        return [(i, c) for i, c in candidates if is_load not in names(c)]

    def deciding_constraints(self, is_load: str | None,
                             flag_cols: tuple[str, ...]) -> list[tuple[int, Any]]:
        out: list[tuple[int, Any]] = []
        mux = self.mux_by_is_load.get(is_load)
        if mux is not None:
            out.append(mux)
        out.extend(self.flag_domain_nonlinear(flag_cols, is_load))
        return out

    def deciding_sources(self, is_load: str | None,
                         flag_cols: tuple[str, ...]) -> tuple[Src, ...]:
        return tuple(Src("constraint", idx)
                     for idx, _ in self.deciding_constraints(is_load, flag_cols))


@dataclass(frozen=True)
class PropagationResult:
    """Propagation state: the derived facts (pins/zeros/exprs) plus the
    ``_DecodingIndex`` used to derive them."""

    pins: dict[str, Pin]
    zeros: tuple[LinZero, ...]
    exprs: tuple[ExprEval, ...]
    decoding: _DecodingIndex

    @functools.cached_property
    def pin_values(self) -> dict[str, int]:
        return {c: p.value for c, p in self.pins.items()}

    @functools.cached_property
    def zero_index(self) -> dict[tuple[tuple[str, int], ...], LinZero]:
        return {z.coeffs: z for z in self.zeros}


def _eval_constraint(expr: Any, env: dict[str, int]) -> int:
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


def _flags_by_access(cols: set[str]) -> dict[int, tuple[str, ...]]:
    out: dict[int, list[str]] = {}
    for c in cols:
        if not c.startswith("flags__"):
            continue
        m = _ACCESS_RE.search(c)
        if m is not None:
            out.setdefault(int(m.group(1)), []).append(c)
    return {a: tuple(sorted(v)) for a, v in out.items()}


def _flag_domain(an: Analysis, flag_cols: tuple[str, ...]) -> dict[str, int] | None:
    """Each flag's proven value-domain size ``n`` (values ``0..n-1``) from the
    certified ``_static_bounds`` — a domain gadget ``f·(f-1)·…·(f-(n-1))=0``
    gives ``Bound[0,n)``.

    Opcode flags are frequently TERNARY, so the refutation must enumerate the
    real domain: assuming ``{0,1}`` refutes a value only because ``f=2`` was
    never tried, pinning a flag (or is_load) that is not actually forced.
    Returns ``None`` if any flag lacks a proven finite ``[0,n)`` domain — then
    no sound enumeration exists and the caller must decline. Also declines when
    the enumeration would blow up: a range-checked column with a wide bound
    (e.g. an 8-bit ``[0,256)``) is not a real opcode flag, and the product of
    domains bounds the ``iproduct`` size, so cap it.
    """
    dom: dict[str, int] = {}
    size = 1
    for c in flag_cols:
        b = an._static_bounds.get(c)
        if b is None or b.lo != 0 or b.hi is None:
            return None
        dom[c] = b.hi
        size *= b.hi
        if size > _MAX_FLAG_ENUM:
            return None
    return dom


def _deciding_covered(deciding: list[Any], known: set[str]) -> bool:
    """True iff every column in the deciding constraints is enumerated or pinned.

    ``_eval_constraint`` reads any column not in the trial env as 0, so a free
    (non-flag, non-solved, non-pinned) column would make the refutation reason
    over a single arbitrary assignment (col = 0) rather than all of them — it
    could then declare a value refuted that is actually reachable, pinning
    wrongly. When a deciding constraint has such a column, decline to pin."""
    return all(col in known for c in deciding for col in names(c))


def _refute_is_load(is_load: str, flag_cols: tuple[str, ...],
                    index: _DecodingIndex, pin_values: dict[str, int],
                    flag_dom: dict[str, int]) -> int | None:
    deciding = [c for _, c in index.deciding_constraints(is_load, flag_cols)]
    if not deciding:
        return None
    if not _deciding_covered(deciding, set(flag_cols) | {is_load} | set(pin_values)):
        return None
    mux = index.mux_by_is_load.get(is_load)
    if mux is None:
        return None
    mux_con = mux[1]
    # is_load has no proven finite domain of its own, so enumerating it over
    # {0,1} would refute a value a ternary/scaled mux still reaches (e.g.
    # is_load = 2*f over boolean f reaches {0,2}, yet {0,1} sees only 0, pinning
    # is_load=0 wrongly). Instead read is_load off the mux -- linear in is_load,
    # a*is_load + g(flags) = 0 -- for every flag assignment in the proven
    # domain, and pin only when that reachable set is a single value.
    reachable: set[int] = set()
    for bits in iproduct(*(range(flag_dom[c]) for c in flag_cols)):
        env = dict(pin_values)
        for col, v in zip(flag_cols, bits):
            env[col] = v
        m0 = _eval_constraint(mux_con, {**env, is_load: 0})
        a = (_eval_constraint(mux_con, {**env, is_load: 1}) - m0) % P
        if a == 0:
            return None   # mux does not determine is_load here: cannot pin
        v_il = (-m0 * pow(a, -1, P)) % P
        if all(_eval_constraint(c, {**env, is_load: v_il}) == 0 for c in deciding):
            reachable.add(v_il)
    return to_signed(reachable.pop()) if len(reachable) == 1 else None


def _surviving_flag_bits(
    flag_cols: tuple[str, ...],
    deciding: list[Any],
    pin_values: dict[str, int],
    flag_dom: dict[str, int],
) -> list[tuple[int, ...]]:
    envs: list[tuple[int, ...]] = []
    for bits in iproduct(*(range(flag_dom[c]) for c in flag_cols)):
        trial = dict(pin_values)
        for col, v in zip(flag_cols, bits):
            trial[col] = v
        if all(_eval_constraint(c, trial) == 0 for c in deciding):
            envs.append(bits)
    return envs


def _refute_flag_value(
    col: str,
    flag_cols: tuple[str, ...],
    deciding: list[Any],
    pin_values: dict[str, int],
    flag_dom: dict[str, int],
) -> int | None:
    if not _deciding_covered(deciding, set(flag_cols) | {col} | set(pin_values)):
        return None
    survivors: list[int] = []
    for v in range(flag_dom[col]):
        trial = dict(pin_values)
        trial[col] = v
        free = [c for c in flag_cols if c not in trial]
        for bits in iproduct(*(range(flag_dom[c]) for c in free)):
            env = dict(trial)
            for c, b in zip(free, bits):
                env[c] = b
            if all(_eval_constraint(c, env) == 0 for c in deciding):
                survivors.append(v)
                break
    return survivors[0] if len(survivors) == 1 else None


def _refute_is_load_pins(pins: dict[str, Pin], pin_values: dict[str, int],
                         an: Analysis, index: _DecodingIndex) -> None:
    cols = an.constraint_cols
    flags = an.flags_by_access
    for is_load in sorted(c for c in cols if c.startswith("is_load_")):
        if is_load in pins:
            continue
        m = _IS_LOAD_RE.match(is_load)
        if m is None:
            continue
        flag_cols = flags.get(int(m.group(1)), ())
        if not flag_cols:
            continue
        flag_dom = _flag_domain(an, flag_cols)
        if flag_dom is None:
            continue
        v = _refute_is_load(is_load, flag_cols, index, pin_values, flag_dom)
        if v is None:
            continue
        prem = tuple(pins.values())
        pins[is_load] = Pin(
            is_load, v,
            sources=index.deciding_sources(is_load, flag_cols),
            premises=prem,
            refute_flags=flag_cols,
        )
        pin_values[is_load] = v


def _refute_flag_pins(pins: dict[str, Pin], pin_values: dict[str, int],
                      an: Analysis, index: _DecodingIndex) -> None:
    """Pin opcode flag bits once is_load and the mux cone fix their value."""
    flags = an.flags_by_access
    for is_load in sorted(c for c in pins if c.startswith("is_load_")):
        m = _IS_LOAD_RE.match(is_load)
        if m is None:
            continue
        flag_cols = flags.get(int(m.group(1)), ())
        if not flag_cols:
            continue
        flag_dom = _flag_domain(an, flag_cols)
        if flag_dom is None:
            continue
        deciding = [c for _, c in index.deciding_constraints(is_load, flag_cols)]
        if not deciding:
            continue
        sources = index.deciding_sources(is_load, flag_cols)
        load_pin = pins[is_load]
        changed = True
        while changed:
            changed = False
            for col in flag_cols:
                if col in pins:
                    continue
                v = _refute_flag_value(col, flag_cols, deciding, pin_values, flag_dom)
                if v is None:
                    continue
                pins[col] = Pin(col, v, sources=sources, premises=(load_pin,))
                pin_values[col] = v
                changed = True


def _accesses_in_expr(expr: Any) -> set[int]:
    out: set[int] = set()
    for col in names(expr):
        m = _ACCESS_RE.search(col)
        if m is not None:
            out.add(int(m.group(1)))
    return out


def surviving_envs(an: Analysis, prop: PropagationResult,
                   ) -> dict[int, list[dict[str, int]]]:
    """Pinned + flag assignments satisfying each access's mux/opcode cone."""
    pin_values = prop.pin_values
    flags = an.flags_by_access
    out: dict[int, list[dict[str, int]]] = {}
    index = prop.decoding
    for is_load in sorted(c for c in pin_values if c.startswith("is_load_")):
        m = _IS_LOAD_RE.match(is_load)
        if m is None:
            continue
        access = int(m.group(1))
        flag_cols = flags.get(access, ())
        if not flag_cols:
            continue
        flag_dom = _flag_domain(an, flag_cols)
        if flag_dom is None:
            continue
        deciding = [c for _, c in index.deciding_constraints(is_load, flag_cols)]
        bits_list = _surviving_flag_bits(flag_cols, deciding, pin_values, flag_dom)
        envs = []
        for bits in bits_list:
            trial = dict(pin_values)
            for col, v in zip(flag_cols, bits):
                trial[col] = v
            envs.append(trial)
        if envs:
            out[access] = envs
    return out


def propagate(an: Analysis) -> PropagationResult:
    """Fixpoint column pins + residual linear zeros (after substitution)."""
    # Kinds-independent bounds from the single oracle (rules.Analysis); these
    # are a subset of `an.bounds`, so every window premise below is a fact that
    # certify.all_facts independently proves.
    bounds = an._static_bounds
    cons = an.machine.get("constraints", [])
    decoding = _DecodingIndex.build(cons)
    raw = [(idx, lf) for idx, c in enumerate(cons) if (lf := linform(c)) is not None]
    pins: dict[str, Pin] = {}
    pin_values: dict[str, int] = {}
    changed = True
    while changed:
        changed = False
        for idx, lf_raw in raw:
            applied = tuple(pins[c] for c in lf_raw.columns if c in pins)
            lf = lf_raw.subst(pin_values)
            if lf.is_const:
                continue
            hit = _try_pin(lf, bounds)
            if hit is not None and hit[0] not in pins:
                col, val, win_bounds = hit
                pins[col] = Pin(col, val,
                                sources=(Src("constraint", idx),),
                                premises=win_bounds + applied)
                pin_values[col] = val
                changed = True

    _refute_is_load_pins(pins, pin_values, an, decoding)
    _refute_flag_pins(pins, pin_values, an, decoding)

    zeros: list[LinZero] = []
    for idx, lf_raw in raw:
        applied = tuple(pins[c] for c in lf_raw.columns if c in pins)
        lf = lf_raw.subst(pin_values)
        if lf.is_const:
            continue
        win = _window_premises(lf, bounds)
        if win is not None and _window_sound(win[0], win[1]):
            zeros.append(LinZero(
                lf.coeffs, lf.const,
                sources=(Src("constraint", idx),),
                premises=win[2] + applied))

    return PropagationResult(pins=pins, zeros=tuple(zeros), exprs=(), decoding=decoding)


def eval_mult(mf: LinForm | None, prop: PropagationResult) -> int | None:
    v, _ = eval_mult_basis(mf, prop)
    return v


def eval_mult_basis(mf: LinForm | None, prop: PropagationResult,
                    ) -> tuple[int | None, tuple[Fact, ...]]:
    if mf is None:
        return None, ()
    prem: list[Fact] = [prop.pins[c] for c in mf.columns if c in prop.pins]
    mf = mf.subst(prop.pin_values)
    if mf.is_const:
        return mf.const % P, tuple(prem)
    zi = prop.zero_index
    zf = zi.get(mf.coeffs)
    if zf is not None:
        return (mf.const - zf.const) % P, tuple(prem) + (zf,)
    zf = zi.get(_neg_coeffs(mf.coeffs))
    if zf is not None:
        return (mf.const + zf.const) % P, tuple(prem) + (zf,)
    return None, ()


_RelPin = tuple[str, int]


def _fold_pins(expr: Any, prop_or_pins: PropagationResult | dict[str, int],
               rel_pins: dict[str, _RelPin] | None = None) -> Any:
    if isinstance(prop_or_pins, dict):
        prop = PropagationResult(
            pins={c: Pin(c, v) for c, v in prop_or_pins.items()},
            zeros=(), exprs=(), decoding=_DecodingIndex({}, {}))
    else:
        prop = prop_or_pins
    pins = prop.pin_values
    if isinstance(expr, int):
        return expr
    if isinstance(expr, str):
        if expr in pins:
            return pins[expr]
        if rel_pins is not None and expr in rel_pins:
            base, off = rel_pins[expr]
            if off == 0:
                return base
            return [base, "+", off]
        return expr
    if isinstance(expr, list) and len(expr) == 2 and expr[0] == "-":
        inner = _fold_pins(expr[1], prop, rel_pins)
        if isinstance(inner, int):
            return to_signed(-inner)
        return ["-", inner]
    if isinstance(expr, list) and len(expr) == 3:
        a = _fold_pins(expr[0], prop, rel_pins)
        b = _fold_pins(expr[2], prop, rel_pins)
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


def _two_col_gap_edges(two_col_gaps: list[tuple[int, str, str, int]],
                        ) -> dict[str, list[tuple[str, int]]]:
    adj: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
    for _idx, pos, neg, const in two_col_gaps:
        gap = -const
        adj[neg].append((pos, gap))
        adj[pos].append((neg, -gap))
    return adj


def _substitution_edges(substitutions: list[Any] | None,
                        ) -> dict[str, list[tuple[str, int]]]:
    adj: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
    if not substitutions:
        return adj
    for pair in substitutions:
        if not (isinstance(pair, list) and len(pair) == 2):
            continue
        var, defn = pair
        if not isinstance(var, str) or isinstance(defn, int):
            continue
        lf = linform(defn)
        if lf is None or len(lf.coeffs) != 1 or lf.coeffs[0][1] != 1:
            continue
        base, off = lf.coeffs[0][0], lf.const
        adj[base].append((var, off))
        adj[var].append((base, -off))
    return adj


def send_ts_aliases(send_cols: set[str],
                    two_col_gaps: list[tuple[int, str, str, int]],
                    substitutions: list[Any] | None,
                    ) -> dict[str, _RelPin]:
    if not send_cols:
        return {}
    raw = _two_col_gap_edges(two_col_gaps)
    for base, edges in _substitution_edges(substitutions).items():
        raw[base].extend(edges)
    adj: dict[str, list[tuple[str, int]]] = collections.defaultdict(list)
    for col, edges in raw.items():
        if col not in send_cols:
            continue
        adj[col] = [(nxt, d) for nxt, d in edges if nxt in send_cols]
    aliases: dict[str, _RelPin] = {}
    seen: set[str] = set()
    for start in sorted(send_cols):
        if start in seen:
            continue
        rel: dict[str, int] = {start: 0}
        queue = [start]
        ok = True
        while queue:
            cur = queue.pop()
            seen.add(cur)
            for nxt, d in adj.get(cur, ()):
                v = rel[cur] + d
                if nxt in rel:
                    if rel[nxt] != v:
                        ok = False
                else:
                    rel[nxt] = v
                    queue.append(nxt)
        if not ok:
            continue
        base = min(rel, key=lambda c: (rel[c], c))
        base_off = rel[base]
        for col, v in rel.items():
            if col in send_cols:
                aliases[col] = (base, v - base_off)
    return aliases


def _rewrite_ts_slot(expr: Any, aliases: dict[str, _RelPin]) -> Any:
    lf = linform(expr)
    if lf is None or len(lf.coeffs) != 1 or lf.coeffs[0][1] != 1:
        return expr
    col, intra = lf.coeffs[0][0], lf.const
    hit = aliases.get(col)
    if hit is None:
        return expr
    base, off = hit
    total = off + intra
    if total == 0:
        return base
    return [base, "+", total]


def _pin_premises_for_expr(expr: Any, prop: PropagationResult) -> tuple[Fact, ...]:
    """Pin facts for columns substituted while folding ``expr``."""
    seen: set[str] = set()
    prem: list[Fact] = []

    def walk(e: Any) -> None:
        if isinstance(e, str) and e in prop.pins and e not in seen:
            seen.add(e)
            prem.append(prop.pins[e])
        elif isinstance(e, list):
            for part in e:
                walk(part)

    walk(expr)
    return tuple(prem)


def _try_refute_expr(expr: Any, prop: PropagationResult,
                     envs_by_access: dict[int, list[dict[str, int]]],
                     ) -> ExprEval | None:
    if isinstance(expr, int):
        return None
    accs = _accesses_in_expr(expr)
    if len(accs) != 1:
        return None
    access = next(iter(accs))
    envs = envs_by_access.get(access)
    if not envs:
        return None
    folded = _fold_pins(expr, prop)
    if isinstance(folded, int):
        value = folded
    else:
        vals: set[int] = set()
        for env in envs:
            v = _eval_partial(folded, env)
            if v is None:
                return None
            vals.add(to_signed(v))
        if len(vals) != 1:
            return None
        value = next(iter(vals))
    cols = set(prop.pin_values) | set(names(expr))
    flags = _flags_by_access(cols)
    flag_cols = flags.get(access, ())
    is_load = None
    for col in prop.pin_values:
        m = _IS_LOAD_RE.match(col)
        if m is not None and int(m.group(1)) == access:
            is_load = col
            break
    # deciding_sources tolerates is_load=None (no mux; flag-domain gadgets only).
    sources = prop.decoding.deciding_sources(is_load, flag_cols) if flag_cols else ()
    return ExprEval(expr, value, access,
                    sources=sources,
                    premises=_pin_premises_for_expr(expr, prop))


def eval_expr(prop: PropagationResult, expr: Any) -> int | None:
    if isinstance(expr, int):
        return to_signed(expr)
    lf = linform(expr)
    if lf is None:
        return None
    v = eval_mult(lf, prop)
    return to_signed(v) if v is not None else None


def simplify_expr(prop: PropagationResult, expr: Any,
                  rel_pins: dict[str, _RelPin] | None = None) -> Any:
    v = eval_expr(prop, expr)
    if v is not None:
        return v
    folded = _fold_pins(expr, prop, rel_pins)
    if isinstance(folded, int):
        return folded
    if folded is not expr:
        v = eval_expr(prop, folded)
        if v is not None:
            return v
        expr = folded
    lf = linform(expr)
    if lf is None:
        return expr
    lf = lf.subst(prop.pin_values)
    return lf.const if lf.is_const else _lf_to_expr(lf)


def simplify_mult(prop: PropagationResult, mult: Any) -> Any:
    lf = linform(mult)
    if lf is None:
        return mult
    v = eval_mult(lf, prop)
    if v is not None:
        return to_signed(v)
    lf = lf.subst(prop.pin_values)
    return lf.const if lf.is_const else _lf_to_expr(lf)


def simplify_mem_row(row: MemRow, prop: PropagationResult,
                     envs_by_access: dict[int, list[dict[str, int]]],
                     ts_aliases: dict[str, _RelPin] | None = None) -> MemRow:
    as_arg = simplify_expr(prop, row.args[0])
    ev = _try_refute_expr(row.args[1], prop, envs_by_access)
    ptr_arg = ev.value if ev is not None else simplify_expr(prop, row.args[1])
    ts_arg = simplify_expr(prop, row.args[-1])
    if ts_aliases:
        ts_arg = _rewrite_ts_slot(ts_arg, ts_aliases)
    args = (as_arg, ptr_arg, *row.args[2:-1], ts_arg)
    return MemRow(row.ordinal, simplify_mult(prop, row.mult), args)


def simplify_mem_rows(mem: list[MemRow], prop: PropagationResult,
                      envs_by_access: dict[int, list[dict[str, int]]],
                      ts_aliases: dict[str, _RelPin] | None = None,
                      ) -> tuple[list[MemRow], tuple[ExprEval, ...]]:
    exprs: list[ExprEval] = []
    out: list[MemRow] = []
    for row in mem:
        ev = _try_refute_expr(row.args[1], prop, envs_by_access)
        if ev is not None:
            exprs.append(ev)
        out.append(simplify_mem_row(row, prop, envs_by_access, ts_aliases))
    return out, tuple(exprs)


def format_debug(an: Analysis) -> str:
    prop = an._propagation
    lines = [f"# propagation pins ({len(prop.pins)})"]
    for col in sorted(prop.pins):
        lines.append(f"  {col} = {prop.pins[col].value}")
    lines.append(f"# propagation zeros ({len(prop.zeros)})")
    for z in prop.zeros:
        lines.append(f"  {z}")
    lines.append(f"# propagation exprs ({len(prop.exprs)})")
    for e in prop.exprs:
        lines.append(f"  {e}")
    lines.append(f"# memory interactions ({len(an.mem)}) after simplification")
    for r in an.mem:
        lines.append(
            f"  #{r.ordinal}  mult={json.dumps(r.mult)}  args={json.dumps(list(r.args))}")
    return "\n".join(lines)
