"""Unit tests for the interface memory encoding: `interface_io_relation`,
`_interface_pointer_eq`, and the preanalysis perfect-alignment abort."""
import pytest

from src.utils.args import parse_args, ARGS
from src.bus_interactions.openvm_memory import (
    LIMB_BASE,
    _bound_of,
    _interface_pointer_eq,
    interface_io_relation,
)
from src.bus_interactions.single_interaction_encoder import BusInteraction
from src.smt.utils import *
from src.verify.membus_analysis import MembusAnalysis
from src.verify.preanalysis import _require_perfect_alignment

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
        with pytest.raises(RuntimeError, match="total 1:1"):
            interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})

    def test_disabled_pair_skips_args(self):
        _args()
        a = [_inter(0, [1, 8, _sym("x"), 5])]
        b = [_inter(0, [1, 8, _sym("y"), 5])]
        rel, _ = interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})
        assert rel.is_true()

    def test_nonconst_mult_aborts(self):
        _args()
        a = [BusInteraction(_sym("is_valid"), [Int(1), Int(8), _sym("x"), Int(5)])]
        b = [_inter(1, [1, 8, _sym("y"), 5])]
        with pytest.raises(RuntimeError, match="mult mismatch or non-const"):
            interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})

    def test_mult_mismatch_aborts(self):
        _args()
        a = [_inter(1, [1, 8, _sym("x"), 5])]
        b = [_inter(P - 1, [1, 8, _sym("y"), 5])]
        with pytest.raises(RuntimeError, match="mult mismatch"):
            interface_io_relation("t", a, b, {0: 0}, bounds_a={}, bounds_b={})

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


def _analysis(n: int, kept: dict[int, int], *, align_ok=True, n_after=None) -> MembusAnalysis:
    from pathlib import Path

    m = n if n_after is None else n_after
    full = dict(kept)
    for i in range(min(n, m)):
        full.setdefault(i, i)
    return MembusAnalysis(
        before_path=Path("b"),
        after_path=Path("a"),
        before_to_after=full,
        before_matches=[set() for _ in range(n)],
        after_matches=[set() for _ in range(m)],
        before_status=[None] * n,
        after_status=[None] * m,
        align_ok=align_ok,
        kept_pairs=kept,
    )


class TestPerfectAlignmentAbort:
    def test_perfect_alignment_accepted(self):
        _args()
        _require_perfect_alignment(_analysis(3, {0: 0, 1: 1, 2: 2}))

    def test_permuted_bijection_accepted(self):
        _args()
        _require_perfect_alignment(_analysis(2, {0: 1, 1: 0}))

    def test_heuristic_fallback_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="membus align did not run"):
            _require_perfect_alignment(
                _analysis(2, {}, align_ok=False)
            )

    def test_partial_kept_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="not total"):
            _require_perfect_alignment(_analysis(2, {0: 0}))

    def test_count_mismatch_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="counts differ"):
            _require_perfect_alignment(
                _analysis(2, {0: 0, 1: 1}, n_after=3)
            )

    def test_non_bijection_aborts(self):
        _args()
        with pytest.raises(RuntimeError, match="bijection"):
            _require_perfect_alignment(_analysis(2, {0: 0, 1: 0}))
