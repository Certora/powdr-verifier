"""Claim forcing for symbolic-key memory matchings — aliasing left open.

The pre-solution for a symbolic-key address space is computed by the same
prefix-interval graph algorithm as AS1, under the **no-aliasing reading**
(every syntactically distinct key class treated as a distinct cell). That is
sufficient for *a* solution: we only ever need some model, and the no-alias
world is one (spread the free bases apart). What the graph reading cannot
provide is entailment: with a memory-loaded base in the space, the alias
partition is not static, so a cell with potential aliasing is **never
unique** and each of its claims is only a guess.

This module upgrades individual guessed claims to **forced**: a claim is
forced iff it holds under EVERY aliasing resolution. Encoding over ℤ, busat
MEM semantics, driven by certified facts:

- one free ``Int`` per base class, one free block-entry clock ``T``;
- pointers are ``BASE + offset`` atoms (a constant pointer is its residue);
- a send's timestamp is ``T + vtime`` (exact, from the Gap web);
- a recv's witness is a free ``Int`` ``pv ≤ T + threshold`` (its RecvUpper
  intersection);
- a match implies pointer *and* timestamp equality; match booleans exist
  only where the timestamp bound allows one;
- every recv matches exactly one send or is an **input** (``pv < T``); a
  send read by no recv is an **output**;
- one entry and one exit record per cell (pointer-distinctness of inputs and
  of outputs); ``#inputs == #outputs``.

Per group ``g`` the encoding contains ``g`` plus every group not provably
disjoint from it (its *cluster*). Provably-disjoint rows can never interact
with ``g`` and are omitted; worlds where an uncertain row pairs OUTSIDE the
cluster are still covered, because the boundary options (free-witness input,
unread send) emulate any external routing. So the cluster's model space
over-approximates every real world's projection onto ``g`` — the direction
forcing needs.

Before any flipping, the mined pre-solution of the whole cluster is asserted
once and must be SAT: this cross-validates the graph solution against the
SMT encoding on every run, and rules out vacuous forcing on an unsatisfiable
encoding. Then each claim of ``g`` is checked by asserting its negation —
UNSAT ⟹ forced.
"""
from __future__ import annotations

import collections
from dataclasses import dataclass

import z3

# Deterministic work budget per cluster (z3 rlimit units, shared by the
# feasibility check and all claim flips). Exhaustion degrades to "unforced",
# never to a wrong answer.
DEFAULT_RLIMIT = 50_000_000

# A group whose cluster exceeds this many interactions is not worth a
# quadratic encoding (pre-`solver` dumps make every cluster the full pool);
# the caller keeps the graph pre-solution and leaves its claims unforced.
DEFAULT_CLUSTER_CAP = 128


@dataclass(frozen=True)
class EngineRow:
    """One active memory interaction, reduced to what the matching needs."""

    ordinal: int
    kind: str          # "send" | "recv"
    base: str | None   # base-class id; None = constant pointer
    offset: int        # constant offset from the base / the constant pointer
    time: int          # send: exact vtime; recv: witness threshold (pv <= T+time)


# A claim mined from the pre-solution:
#   ("edge", recv_ordinal, send_ordinal) — the recv reads that send;
#   ("input", recv_ordinal)             — the recv reads the entry value;
#   ("output", send_ordinal)            — the send escapes (read by no recv).
Claim = tuple


def cluster_size(groups: list[list[EngineRow]], uncertain: dict[int, set[int]],
                 gi: int) -> int:
    return len(groups[gi]) + sum(len(groups[h]) for h in uncertain.get(gi, set()))


def force_group(groups: list[list[EngineRow]], uncertain: dict[int, set[int]],
                gi: int, claims_by_group: dict[int, list[Claim]],
                rlimit: int = DEFAULT_RLIMIT) -> dict[Claim, bool]:
    """Force each claim of group ``gi`` against its cluster, aliasing open.

    ``claims_by_group`` holds the mined pre-solution claims of every group
    (used whole-cluster for the feasibility cross-check). Returns
    ``claim -> forced`` for ``claims_by_group[gi]``. Raises ``ValueError``
    when the cluster encoding is unsatisfiable (no matching at all — a
    degenerate bus) or the pre-solution is not one of its models (an
    engine-disagreement bug, never to be papered over).
    """
    cluster = [(gi, r) for r in groups[gi]]
    for h in sorted(uncertain.get(gi, set())):
        cluster += [(h, r) for r in groups[h]]
    cluster_groups = {gi, *uncertain.get(gi, set())}

    def could_alias(g1: int, g2: int) -> bool:
        return g1 == g2 or g2 in uncertain.get(g1, set())

    s = z3.Solver()
    s.set("rlimit", rlimit)
    t = z3.Int("T")
    bases: dict[str, z3.ArithRef] = {}

    def ptr(row: EngineRow):
        if row.base is None:
            return z3.IntVal(row.offset)
        return bases.setdefault(row.base, z3.Int(f"B_{row.base}")) + row.offset

    sends = [(g, r) for g, r in cluster if r.kind == "send"]
    recvs = [(g, r) for g, r in cluster if r.kind == "recv"]
    pv = {r.ordinal: z3.Int(f"pv_{r.ordinal}") for _, r in recvs}
    inp = {r.ordinal: z3.Bool(f"in_{r.ordinal}") for _, r in recvs}

    # match booleans, only where the timestamp bound admits one: a recv can
    # only take a send at or below its threshold (RecvUpper is a fact).
    m: dict[tuple[int, int], z3.BoolRef] = {}
    readers: dict[int, list[z3.BoolRef]] = collections.defaultdict(list)
    for rg, r in recvs:
        s.add(pv[r.ordinal] <= t + r.time)
        s.add(z3.Implies(inp[r.ordinal], pv[r.ordinal] < t))
        options = [inp[r.ordinal]]
        for sg, snd in sends:
            if snd.time > r.time or not could_alias(rg, sg):
                continue
            mv = z3.Bool(f"m_{r.ordinal}_{snd.ordinal}")
            m[(r.ordinal, snd.ordinal)] = mv
            eqs = [pv[r.ordinal] == t + snd.time]
            if rg != sg:                       # same group = same cell = same pointer
                eqs.append(ptr(r) == ptr(snd))
            s.add(z3.Implies(mv, z3.And(eqs)))
            options.append(mv)
            readers[snd.ordinal].append(mv)
        s.add(z3.AtMost(*options, 1))
        s.add(z3.AtLeast(*options, 1))

    out = {snd.ordinal: z3.Bool(f"out_{snd.ordinal}") for _, snd in sends}
    for _, snd in sends:
        rd = readers[snd.ordinal]
        if rd:
            s.add(z3.AtMost(*rd, 1))
        s.add(out[snd.ordinal] == z3.Not(z3.Or(rd)))

    # one entry record and one exit record per cell: two inputs (outputs) at
    # the same pointer are impossible. Pairs of provably-disjoint groups are
    # distinct by construction and need no constraint.
    def distinct_pairs(items):
        for i, (g1, r1) in enumerate(items):
            for g2, r2 in items[i + 1:]:
                if could_alias(g1, g2):
                    yield r1, r2, g1 == g2

    for r1, r2, same_cell in distinct_pairs(recvs):
        both = z3.And(inp[r1.ordinal], inp[r2.ordinal])
        s.add(z3.Not(both) if same_cell else z3.Implies(both, ptr(r1) != ptr(r2)))
    for s1, s2, same_cell in distinct_pairs(sends):
        both = z3.And(out[s1.ordinal], out[s2.ordinal])
        s.add(z3.Not(both) if same_cell else z3.Implies(both, ptr(s1) != ptr(s2)))

    s.add(z3.Sum([z3.If(b, 1, 0) for b in inp.values()])
          == z3.Sum([z3.If(b, 1, 0) for b in out.values()]))

    def lit(claim: Claim):
        if claim[0] == "edge":
            return m[(claim[1], claim[2])]
        if claim[0] == "input":
            return inp[claim[1]]
        return out[claim[1]]

    # feasibility + cross-validation: the whole cluster's mined pre-solution
    # must be a model of the open encoding (the no-alias world realizes it)
    feas = [lit(c) for h in sorted(cluster_groups)
            for c in claims_by_group.get(h, [])]
    s.push()
    s.add(feas)
    res = s.check()
    s.pop()
    if res == z3.unsat:
        if s.check() == z3.unsat:
            raise ValueError(
                "solve: cluster admits no matching at all (unsatisfiable memory bus)")
        raise ValueError(
            "solve: internal cross-check failed -- the graph pre-solution is not "
            "a model of the SMT encoding (engine disagreement)")
    if res != z3.sat:                          # budget exhausted: nothing forced
        return dict.fromkeys(claims_by_group.get(gi, []), False)

    forced: dict[Claim, bool] = {}
    for claim in claims_by_group.get(gi, []):
        s.push()
        s.add(z3.Not(lit(claim)))
        forced[claim] = s.check() == z3.unsat  # holds under EVERY aliasing resolution
        s.pop()
    return forced
