"""Unit tests for the interface memory encoding: `interface_io_relation`,
`_interface_pointer_eq`, internal forced recv<->send pairs, and the
preanalysis alignment abort."""
import pytest

from src.utils.args import parse_args, ARGS
from src.bus_interactions.openvm_memory import (
    LIMB_BASE,
    _bound_of,
    _interface_pointer_eq,
    interface_io_relation,
    internal_pair_equalities,
)
from src.bus_interactions.single_interaction_encoder import BusInteraction
from src.smt.utils import *
from src.verify.membus_analysis import (
    Info,
    MembusAnalysis,
    _collect_internal_pairs,
)
from src.verify.preanalysis import _require_interface_alignment

P = 2013265921


def _args(*extra: str) -> None:
    parse_args(["--memory-encoding", "interface", *extra, "check", "x"])


def _inter(mult: int, args: list) -> BusInteraction:
    conv = [Int(a) if isinstance(a, int) else a for a in args]
    return BusInteraction(Int(mult), conv)


def _sym(name: str) -> FNode:
    return Symbol(name, INT)


def _relation_eqs(rel: FNode) -> list[FNode]:
    return list(rel.args()) if rel.is_and() else [rel]


class TestInterfaceIoRelation:
    def test_identity_map_full_equalities(self):
        _args()
        x, y = _sym("x"), _sym("y")
        a = [_inter(1, [1, 8, x, 5])]
        b = [_inter(1, [1, 8, y, 5])]
        rel, syms = interface_io_relation(
            "t", a, b, {0: 0}, bounds_a={}, bounds_b={}
        )
        assert syms == frozenset()
        # mult eq + 4 arg equalities; the data equality must relate x and y
        free = rel.get_free_variables()
        assert x in free and y in free

    def test_permuted_bijection(self):
        _args()
        a = [_inter(1, [1, 8, _sym("x0"), 5]), _inter(1, [1, 4, _sym("x1"), 6])]
        b = [_inter(1, [1, 4, _sym("y1"), 6]), _inter(1, [1, 8, _sym("y0"), 5])]
        rel, _ = interface_io_relation(
            "t", a, b, {0: 1, 1: 0}, bounds_a={}, bounds_b={}
        )
        free = {str(v) for v in rel.get_free_variables()}
        assert {"x0", "y0", "x1", "y1"} <= free

    def test_partial_map_aborts(self):
        _args()
        a = [_inter(1, [1, 8, _sym("x"), 5]), _inter(1, [1, 4, _sym("z"), 6])]
        b = [_inter(1, [1, 8, _sym("y"), 5]), _inter(1, [1, 4, _sym("w"), 6])]
        with pytest.raises(RuntimeError, match="disjoint cover"):
            interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})

    def test_partial_map_with_internal_legs_accepted(self):
        """A before-side internal pair (ordinals 1,2) is excused from the kept
        map when declared via ``internal_a``; its equalities live on its own
        side, not in the io relation."""
        _args()
        a = [
            _inter(1, [1, 8, _sym("x"), 5]),
            _inter(P - 1, [1, 4, _sym("r"), _sym("rt")]),
            _inter(1, [1, 4, _sym("s"), 6]),
        ]
        b = [_inter(1, [1, 8, _sym("y"), 5])]
        rel, _ = interface_io_relation(
            "t", a, b, {0: 0}, bounds_a={}, bounds_b={},
            internal_a=frozenset({1, 2}),
        )
        free = {str(v) for v in rel.get_free_variables()}
        assert {"x", "y"} <= free
        assert not {"r", "s", "rt"} & free

    def test_internal_leg_overlapping_kept_aborts(self):
        _args()
        a = [_inter(1, [1, 8, _sym("x"), 5])]
        b = [_inter(1, [1, 8, _sym("y"), 5])]
        with pytest.raises(RuntimeError, match="disjoint cover"):
            interface_io_relation(
                "t", a, b, {0: 0}, bounds_a={}, bounds_b={},
                internal_a=frozenset({0}),
            )

    def test_disabled_pair_skips_args(self):
        _args()
        a = [_inter(0, [1, 8, _sym("x"), 5])]
        b = [_inter(0, [1, 8, _sym("y"), 5])]
        rel, _ = interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})
        assert rel.is_true()

    # `--interface-ignore-checks` (default ON) downgrades these aborts to a warning
    # and equates the pair anyway; the abort is what the flag switches back on. The
    # flag postdates these tests, which is why they need it explicitly.
    def test_nonconst_mult_aborts(self):
        _args("--no-interface-ignore-checks")
        a = [BusInteraction(_sym("is_valid"), [Int(1), Int(8), _sym("x"), Int(5)])]
        b = [_inter(1, [1, 8, _sym("y"), 5])]
        with pytest.raises(RuntimeError, match="mult mismatch or non-const"):
            interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})

    def test_mult_mismatch_aborts(self):
        _args("--no-interface-ignore-checks")
        a = [_inter(1, [1, 8, _sym("x"), 5])]
        b = [_inter(P - 1, [1, 8, _sym("y"), 5])]
        with pytest.raises(RuntimeError, match="mult mismatch"):
            interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})

    def test_nonconst_mult_is_equated_when_checks_ignored(self):
        """The default path: no abort, a loud warning, and the pair is equated
        anyway (`--interface-ignore-checks`). Pins the behaviour the two tests above
        switch off, so a change to either direction is visible."""
        _args()
        a = [BusInteraction(_sym("is_valid"), [Int(1), Int(8), _sym("x"), Int(5)])]
        b = [_inter(1, [1, 8, _sym("y"), 5])]
        rel, _ = interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})
        assert not rel.is_false()

    def test_recv_mult_expression_folds(self):
        """`(- 1)`-style mults (the inlining pass output) const-eval to p-1."""
        _args()
        m = Minus(Int(0), Int(1))
        a = [BusInteraction(m, [Int(1), Int(8), _sym("x"), Int(5)])]
        b = [BusInteraction(Int(P - 1), [Int(1), Int(8), _sym("y"), Int(5)])]
        rel, _ = interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})
        assert not rel.is_false()


def _packed(lo: FNode, hi: FNode) -> FNode:
    return Plus(lo, Times(Int(LIMB_BASE), hi))


class TestLimbSplit:
    def _bounds(self, lo: FNode, hi: FNode, blo=65535, bhi=8191):
        return {wrap_mod(lo): blo, wrap_mod(hi): bhi}

    def test_split_applies(self):
        _args()
        lo, hi = _sym("b_lo"), _sym("b_hi")
        lo2, hi2 = _sym("a_lo"), _sym("a_hi")
        eqs = _interface_pointer_eq(
            _packed(lo, hi),
            _packed(lo2, hi2),
            self._bounds(lo, hi),
            self._bounds(lo2, hi2),
        )
        assert eqs is not None and len(eqs) == 2

    def test_split_withheld_missing_bound(self):
        _args()
        lo, hi = _sym("b_lo"), _sym("b_hi")
        lo2, hi2 = _sym("a_lo"), _sym("a_hi")
        eqs = _interface_pointer_eq(
            _packed(lo, hi),
            _packed(lo2, hi2),
            {wrap_mod(hi): 8191},  # lo unbounded
            self._bounds(lo2, hi2),
        )
        assert eqs is None

    def test_split_withheld_wraps_field(self):
        """Limb bounds < 2^16 alone are NOT sufficient: full 32-bit packing
        exceeds BabyBear P and wraps."""
        _args()
        lo, hi = _sym("b_lo"), _sym("b_hi")
        lo2, hi2 = _sym("a_lo"), _sym("a_hi")
        eqs = _interface_pointer_eq(
            _packed(lo, hi),
            _packed(lo2, hi2),
            self._bounds(lo, hi, blo=65535, bhi=65535),
            self._bounds(lo2, hi2, blo=65535, bhi=65535),
        )
        assert eqs is None

    def test_split_withheld_coeff_mismatch(self):
        _args()
        lo, hi = _sym("b_lo"), _sym("b_hi")
        lo2, hi2 = _sym("a_lo"), _sym("a_hi")
        eqs = _interface_pointer_eq(
            Plus(lo, Times(Int(256), hi)),
            _packed(lo2, hi2),
            self._bounds(lo, hi),
            self._bounds(lo2, hi2),
        )
        assert eqs is None

    def test_scaled_bound_lookup(self):
        """`(c*t mod P) <= hi` yields t <= (c^{-1} mod P)*hi when no wrap —
        the OpenVM pointer-alignment shape (c = 4^{-1} mod P)."""
        _args()
        t = _sym("lo_limb")
        c = pow(4, -1, P)
        bounds = {wrap_mod(Times(Int(c), t)): 16383}
        assert _bound_of(t, bounds) == 4 * 16383

    def test_scaled_bound_negated_shape(self):
        """`((0 - c*t) mod P) < B` (post-inlining constant folding) also
        resolves: -c is inverted mod P."""
        _args()
        t = _sym("lo_limb")
        c = P - pow(4, -1, P)
        bounds = {wrap_mod(Minus(Int(0), Times(Int(c), t))): 16383}
        assert _bound_of(t, bounds) == 4 * 16383

    def test_flag_disables_split(self):
        _args("--no-interface-limb-split")
        lo, hi = _sym("b_lo"), _sym("b_hi")
        lo2, hi2 = _sym("a_lo"), _sym("a_hi")
        a = [BusInteraction(Int(1), [Int(2), _packed(lo, hi), _sym("d"), Int(5)])]
        b = [BusInteraction(Int(1), [Int(2), _packed(lo2, hi2), _sym("e"), Int(5)])]
        rel, _ = interface_io_relation(
            "t", a, b, {0: 0},
            bounds_a=self._bounds(lo, hi),
            bounds_b=self._bounds(lo2, hi2),
        )
        # packed equality: lo appears only inside a single (mod (- packed packed) P) atom
        eqs = [e for e in _relation_eqs(rel) if lo in e.get_free_variables()]
        assert len(eqs) == 1 and hi in eqs[0].get_free_variables()


def _analysis(
    n: int,
    kept: dict[int, int],
    *,
    n_after=None,
    internal_pairs=(),
    inert=frozenset(),
) -> MembusAnalysis:
    from pathlib import Path

    m = n if n_after is None else n_after
    full = dict(kept)
    for i in range(min(n, m)):
        full.setdefault(i, i)
    legs = {x for pair in internal_pairs for x in pair}
    removed = legs | set(inert)
    # Encode the forced interior pairs as mutual match-singletons, exactly as
    # the worklist would leave them; mark inert ordinals disabled. `removed` is
    # the per-interaction classification the precondition now reads.
    before_matches: list[list[int]] = [[] for _ in range(n)]
    for r, s in internal_pairs:
        before_matches[r] = [s]
        before_matches[s] = [r]
    before_info = [
        Info(None, None, i in inert, None, i in removed) for i in range(n)
    ]
    return MembusAnalysis(
        before_path=Path("b"),
        after_path=Path("a"),
        before_to_after=full,
        before_matches=before_matches,
        after_matches=[[] for _ in range(m)],
        before_info=before_info,
        after_info=[Info(None, None, False, None, False) for _ in range(m)],
        kept_pairs=kept,
    )


class TestInterfaceAlignmentAbort:
    def test_perfect_alignment_accepted(self):
        _args()
        _require_interface_alignment(_analysis(3, {0: 0, 1: 1, 2: 2}))

    def test_permuted_bijection_accepted(self):
        _args()
        _require_interface_alignment(_analysis(2, {0: 1, 1: 0}))

    def test_heuristic_fallback_aborts(self):
        # No align ran => empty kept map and nothing marked removed, so the
        # coverage check (not the removed align_ok flag) rejects it.
        _args()
        with pytest.raises(RuntimeError, match="not fully accounted for"):
            _require_interface_alignment(_analysis(2, {}))

    def test_partial_kept_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="not fully accounted"):
            _require_interface_alignment(_analysis(2, {0: 0}))

    def test_count_mismatch_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="bijection"):
            _require_interface_alignment(
                _analysis(2, {0: 0, 1: 1}, n_after=3)
            )

    def test_non_bijection_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="bijection"):
            _require_interface_alignment(_analysis(2, {0: 0, 1: 0}))

    def test_internal_pairs_cover_removed(self):
        """The 2099600 010->011 shape: 10 before, 6 kept, pairs (6,5), (8,7)."""
        _args()
        kept = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 9: 5}
        _require_interface_alignment(
            _analysis(10, kept, n_after=6, internal_pairs=[(6, 5), (8, 7)])
        )

    def test_uncovered_removed_ordinal_aborts(self):
        _args()
        kept = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 9: 5}
        with pytest.raises(RuntimeError, match="not fully accounted"):
            _require_interface_alignment(
                _analysis(10, kept, n_after=6, internal_pairs=[(6, 5)])
            )

    def test_inert_removed_accepted(self):
        _args()
        _require_interface_alignment(
            _analysis(3, {0: 0, 1: 1}, n_after=2, inert={2})
        )

    def test_leg_overlapping_kept_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="overlap"):
            _require_interface_alignment(
                _analysis(3, {0: 0, 1: 1, 2: 2}, internal_pairs=[(1, 2)])
            )

    def test_duplicate_leg_aborts(self):
        _args()
        kept = {0: 0}
        with pytest.raises(RuntimeError, match="forced mutual singleton"):
            _require_interface_alignment(
                _analysis(4, kept, n_after=1, internal_pairs=[(1, 2), (3, 2)])
            )

    def test_strict_mode_rejects_internal_pairs(self):
        _args("--no-interface-internal-pairs")
        kept = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 9: 5}
        with pytest.raises(RuntimeError, match="no-interface-internal-pairs"):
            _require_interface_alignment(
                _analysis(10, kept, n_after=6, internal_pairs=[(6, 5), (8, 7)])
            )


class TestInternalPairEqualities:
    def _pair_interactions(self):
        """2099600-shaped internal pair: send #5 writes data [148, 9, 32, 0] at
        ts, recv #6 reads free columns with a free prev_timestamp."""
        send = _inter(1, [1, 4, Int(148), Int(9), Int(32), Int(0), _sym("ts")])
        recv = _inter(
            P - 1,
            [1, 4, _sym("d0"), _sym("d1"), _sym("d2"), _sym("d3"), _sym("prev_ts")],
        )
        return [send, recv]

    def test_full_tuple_equalities(self):
        _args()
        inters = self._pair_interactions()
        eqs = internal_pair_equalities("t", inters, [(0, 1)])
        assert len(eqs) == 7  # addr_space, ptr, 4 data limbs, timestamp
        # positional: the last equality relates prev_ts and ts
        last_free = {str(v) for v in eqs[-1].get_free_variables()}
        assert last_free == {"prev_ts", "ts"}
        d0_eqs = [e for e in eqs if "d0" in {str(v) for v in e.get_free_variables()}]
        assert len(d0_eqs) == 1

    def test_field_equality_shape(self):
        """Equalities are mod-P (field), not syntactic Int `=`."""
        _args()
        inters = self._pair_interactions()
        eqs = internal_pair_equalities("t", inters, [(0, 1)])
        ts_eq = eqs[-1]
        assert ts_eq.is_equals()
        mods = [a for a in ts_eq.args() if a.is_mod()]
        assert mods, "expected a wrap_mod((recv - send)) == 0 shape"

    def test_no_limb_split(self):
        """Pointer args are equated packed — keys are just data here."""
        _args()
        lo, hi = _sym("lo"), _sym("hi")
        lo2, hi2 = _sym("lo2"), _sym("hi2")
        send = _inter(1, [2, Plus(lo, Times(Int(LIMB_BASE), hi)), Int(0), Int(9)])
        recv = _inter(
            P - 1, [2, Plus(lo2, Times(Int(LIMB_BASE), hi2)), _sym("d"), _sym("pt")]
        )
        eqs = internal_pair_equalities("t", [send, recv], [(0, 1)])
        ptr_eqs = [e for e in eqs if lo in e.get_free_variables()]
        assert len(ptr_eqs) == 1 and hi in ptr_eqs[0].get_free_variables()

    def test_order_independent(self):
        """Pair ordinals are unordered; recv/send are recovered from the mults,
        so either ordering yields the same tuple of equalities."""
        _args()
        inters = self._pair_interactions()
        for pair in [(0, 1), (1, 0)]:
            eqs = internal_pair_equalities("t", inters, [pair])
            assert len(eqs) == 7
            assert {str(v) for v in eqs[-1].get_free_variables()} == {"prev_ts", "ts"}

    def test_two_sends_abort(self):
        """Neither leg has the recv multiplicity (-1) — no recv/send split."""
        _args()
        send = _inter(1, [1, 4, Int(0), Int(9)])
        send2 = _inter(1, [1, 4, _sym("d"), _sym("pt")])
        with pytest.raises(RuntimeError, match="not \\(recv -1, send \\+1\\)"):
            internal_pair_equalities("t", [send, send2], [(0, 1)])

    def test_nonconst_mult_aborts(self):
        _args()
        send = _inter(1, [1, 4, Int(0), Int(9)])
        recv = BusInteraction(_sym("is_valid"), [Int(1), Int(4), _sym("d"), _sym("pt")])
        with pytest.raises(RuntimeError, match="not \\(recv -1, send \\+1\\)"):
            internal_pair_equalities("t", [send, recv], [(0, 1)])

    def test_arity_mismatch_aborts(self):
        _args()
        send = _inter(1, [1, 4, Int(0), Int(9)])
        recv = _inter(P - 1, [1, 4, _sym("d0"), _sym("d1"), _sym("pt")])
        with pytest.raises(ValueError):
            internal_pair_equalities("t", [send, recv], [(0, 1)])


def _align_row(bid, kind, status, role, partners, after_id=None):
    return {
        "before_id": bid,
        "kind": kind,
        "key": "const 4",
        "status": status,
        "after_id": after_id,
        "local_role": role,
        "local_partners": partners,
        "io": "in" if role == "input" else "out" if role == "output" else "",
        "vtime": "",
    }


class TestCollectInternalPairs:
    def _rows_2099600(self):
        """Shape of the 2099600 010->011 AS1 align: 6 kept, pairs (6,5), (8,7)."""
        rows = [
            _align_row(i, "recv" if i % 2 == 0 else "send", "kept", "input", [], i)
            for i in range(5)
        ]
        rows += [
            _align_row(5, "send", "removed", "interior", [6]),
            _align_row(6, "recv", "removed", "interior", [5]),
            _align_row(7, "send", "removed", "interior", [8]),
            _align_row(8, "recv", "removed", "interior", [7]),
            _align_row(9, "send", "kept", "output", [], 5),
        ]
        return rows

    def test_pairs_collected(self):
        pairs, inert = _collect_internal_pairs(self._rows_2099600(), 1)
        assert {(p.recv, p.send) for p in pairs} == {(6, 5), (8, 7)}
        assert all(p.addr_space == 1 for p in pairs)
        assert inert == set()

    def test_disabled_removed_is_inert(self):
        rows = [
            _align_row(0, "recv", "kept", "input", [], 0),
            _align_row(1, "disabled", "removed", "inert", []),
        ]
        pairs, inert = _collect_internal_pairs(rows, 1)
        assert pairs == [] and inert == {1}

    def test_recv_without_partner_aborts(self):
        rows = [_align_row(0, "recv", "removed", "interior", [])]
        with pytest.raises(RuntimeError, match="not a forced interior"):
            _collect_internal_pairs(rows, 1)

    def test_partner_kept_aborts(self):
        rows = [
            _align_row(0, "send", "kept", "interior", [1], 0),
            _align_row(1, "recv", "removed", "interior", [0]),
        ]
        with pytest.raises(RuntimeError, match="not a matching removed interior send"):
            _collect_internal_pairs(rows, 1)

    def test_partner_not_backlinked_aborts(self):
        rows = [
            _align_row(0, "send", "removed", "interior", [2]),
            _align_row(1, "recv", "removed", "interior", [0]),
            _align_row(2, "recv", "removed", "interior", [0]),
        ]
        with pytest.raises(RuntimeError, match="claimed by more than one|not a matching"):
            _collect_internal_pairs(rows, 1)

    def test_unclaimed_send_aborts(self):
        rows = [_align_row(0, "send", "removed", "interior", [1])]
        with pytest.raises(RuntimeError, match="not\\s+claimed by any removed recv"):
            _collect_internal_pairs(rows, 1)

    def test_boundary_removed_aborts(self):
        rows = [_align_row(0, "recv", "removed", "input", [])]
        with pytest.raises(RuntimeError, match="not a forced interior"):
            _collect_internal_pairs(rows, 1)
