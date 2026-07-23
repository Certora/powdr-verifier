"""Typed facts with premises — the unit of justified extraction.

Every deduction membus makes (a timestamp gap, a recv bound, an affine pointer
decomposition, a resolved multiplicity) is represented as a **fact**: a frozen
dataclass carrying

- the claim itself (typed fields, canonical integers);
- ``sources`` — references to the trusted material it was extracted from
  (constraint indices / bus-interaction ordinals in the dump);
- ``premises`` — other facts it depends on (e.g. the limb bounds a recv bound
  needs); and
- ``assumptions`` — the **named external assumptions** it uses directly.

Nothing here is trusted because of how it was computed: each fact type knows
how to state its own proof obligation, and ``certify.py`` turns any fact into
an SMT query (sources + premises + assumptions ⊢ claim) that must be UNSAT
when the claim is negated. A rule bug shows up as a SAT certificate, not as a
wrong answer downstream.

Assumptions are deliberately explicit and few. They are the only things the
checker takes on faith, and every certificate that uses one shows it.
"""
from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import Any, Iterator


class Assumption(enum.Enum):
    """Named external premises — facts about the openvm pipeline that are not
    derivable from a dump and must be taken on faith (and stated in every
    certificate that uses them).

    Both assumptions are **positional**: they attach to argument slots of the
    memory bus, never to column names. Nothing in the fact layer depends on
    naming conventions (names appear only in human-facing labels)."""

    #: Columns of the block's **clock web** hold integers in ``[0, 2^29)``.
    #: The clock web is structural: a column occurring in the memory-bus
    #: timestamp slot (``args[6]``, shape ``col + off``) is a clock — the
    #: owning instruction's start time — and a column linked to a clock by a
    #: two-column ±1 constraint (the from_state chain, including instructions
    #: with no memory access) is a clock too. openvm's offline memory checker
    #: keeps all clocks in this range; no dump carries the bound. Needed to
    #: read field equations over timestamps as integer equations (no wrap mod
    #: p). Forward gap links (later = earlier + gap) get a *derived* bound
    #: instead of the assumption; only slot seeds and backward links consume
    #: it.
    TS_BOUND = "clock-web columns (ts slots + gap-linked) lie in [0, 2^29)"

    #: Data received from the memory bus is byte-valued: the four data args of
    #: a **recv** interaction are integers in ``[0, 2^8)``. (Writes are the
    #: circuit's obligation, reads are this assumption.)
    MEMBUS_BYTE = "memory-bus recv data are bytes"

    #: When one single column gates EVERY memory interaction's multiplicity
    #: (``mult = ±g`` — structurally recognized, the final exported APC's
    #: activation selector), ``--assume-is-valid`` takes ``g = 1``: the
    #: analysis is conditional on the block actually executing.
    ACTIVE_SELECTOR = "the common activation selector is 1 (block executes)"


TS_BITS = 29
TS_MAX = 1 << TS_BITS   # exclusive upper bound under Assumption.TS_BOUND


@dataclass(frozen=True)
class Src:
    """Reference to trusted source material in the dump."""

    kind: str    # "constraint" | "bus"
    index: int   # constraint index / bus_interactions index

    def __str__(self) -> str:
        return f"{self.kind}[{self.index}]"


@dataclass(frozen=True)
class Fact:
    sources: tuple[Src, ...] = field(kw_only=True, default=())
    premises: tuple["Fact", ...] = field(kw_only=True, default=())
    assumptions: frozenset[Assumption] = field(kw_only=True, default=frozenset())

    def all_assumptions(self) -> frozenset[Assumption]:
        """Direct + transitive assumptions (through premise facts)."""
        acc = set(self.assumptions)
        for p in self.premises:
            acc |= p.all_assumptions()
        return frozenset(acc)

    def walk(self) -> Iterator["Fact"]:
        """This fact and all its premise facts (pre-order, may repeat)."""
        yield self
        for p in self.premises:
            yield from p.walk()


@dataclass(frozen=True)
class Bound(Fact):
    """``col`` holds an integer in ``[lo, hi)`` (``hi=None`` ⟹ only ``≥ lo``)."""

    col: str
    lo: int
    hi: int | None

    def __str__(self) -> str:
        hi = "inf" if self.hi is None else self.hi
        return f"{self.col} in [{self.lo}, {hi})"


@dataclass(frozen=True)
class Gap(Fact):
    """``later == earlier + gap`` as integers (``gap > 0``); both are
    from_state timestamp columns."""

    later: str
    earlier: str
    gap: int

    def __str__(self) -> str:
        return f"{self.later} = {self.earlier} + {self.gap}"


@dataclass(frozen=True)
class RecvUpper(Fact):
    """``pv ≤ fs + const`` as integers — the LessThan gadget's guarantee that
    a recv's previous-timestamp witness precedes its own op's send time."""

    pv: str
    fs: str
    const: int

    def __str__(self) -> str:
        return f"{self.pv} <= {self.fs} + {self.const}"


@dataclass(frozen=True)
class AffineDef(Fact):
    """``col ≡ Σ weight·other + offset (mod modulus)`` as integers — a
    byte-decomposition gadget solved for ``col``.

    ``modulus=None`` means exact integer equality (the gadget admits only the
    chosen root in the window). A finite modulus records that the gadget's
    other root IS feasible and sits exactly ``modulus`` away — the carry case
    of a 16-bit address add gives ``modulus = 2^16``: the gadget determines
    the value **mod 2^16** (the low-16-bit decomposition), nothing stronger.
    """

    col: str
    weights: tuple[tuple[str, int], ...]   # sorted, nonzero
    offset: int
    modulus: int | None

    def __str__(self) -> str:
        ws = " + ".join(f"{w}*{o}" for o, w in self.weights)
        mod = "" if self.modulus is None else f" (mod {self.modulus})"
        return f"{self.col} = {ws} + {self.offset}{mod}"


@dataclass(frozen=True)
class EffKind(Fact):
    """A memory interaction's effective direction: its multiplicity resolves
    to +1 (``send``), −1 (``recv``) or 0 (``disabled``)."""

    ordinal: int    # membus ordinal
    kind: str       # "send" | "recv" | "disabled"

    def __str__(self) -> str:
        return f"mem#{self.ordinal} is {self.kind}"


@dataclass(frozen=True)
class Pin(Fact):
    """``col`` holds integer ``value`` — a single-column propagation pin."""

    col: str
    value: int
    # flag columns for is_load refutation certificates (empty for constraint pins)
    refute_flags: tuple[str, ...] = field(kw_only=True, default=())

    def __str__(self) -> str:
        return f"{self.col} = {self.value}"


@dataclass(frozen=True)
class LinZero(Fact):
    """``Σ coeff·col + const = 0`` as integers — a propagated linear identity."""

    coeffs: tuple[tuple[str, int], ...]
    const: int

    def __str__(self) -> str:
        parts = [f"{v}*{k}" for k, v in self.coeffs]
        if self.const or not parts:
            parts.append(str(self.const))
        return " + ".join(parts) + " = 0"


@dataclass(frozen=True)
class ExprEval(Fact):
    """A dump expression evaluates to ``value`` under every surviving flag env."""

    expr: Any
    value: int
    access: int

    def __str__(self) -> str:
        return f"expr@access{self.access} = {self.value}"
