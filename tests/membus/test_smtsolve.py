"""smtsolve engine: claim forcing with aliasing left open."""
import pytest

from src.membus.smtsolve import EngineRow, force_group


def _send(o, base, off, vt):
    return EngineRow(o, "send", base, off, vt)


def _recv(o, base, off, thr):
    return EngineRow(o, "recv", base, off, thr)


# cell chain used throughout: s0@T+1, input recv (thr 0), out send @T+4,
# interior recv (thr 2) reading s0 — mined claims of its prefix solution:
def _cell(base="b1"):
    return [_send(0, base, 0, 1), _recv(1, base, 0, 0),
            _send(2, base, 0, 4), _recv(3, base, 0, 2)]


CELL_CLAIMS = [("edge", 3, 0), ("input", 1), ("output", 2)]


def test_no_uncertainty_all_forced():
    f = force_group([_cell()], {}, 0, {0: CELL_CLAIMS})
    assert f == {("edge", 3, 0): True, ("input", 1): True, ("output", 2): True}


def test_open_aliasing_interior_forced_boundary_not():
    # a foreign base (memory-loaded pointer) that may alias the cell: the
    # interior edge stays forced (the foreign send is too late for the
    # interior recv), but the boundary can reroute through the foreign pair.
    foreign = [_send(4, "b2", 0, 10), _recv(5, "b2", 0, 9)]
    groups = [_cell(), foreign]
    unc = {0: {1}, 1: {0}}
    claims = {0: CELL_CLAIMS, 1: [("input", 5), ("output", 4)]}
    f0 = force_group(groups, unc, 0, claims)
    assert f0[("edge", 3, 0)] is True
    assert f0[("input", 1)] is True              # thr 0: below every send
    assert f0[("output", 2)] is False            # foreign recv could read it
    f1 = force_group(groups, unc, 1, claims)
    assert f1[("input", 5)] is False             # could read main's out send
    assert f1[("output", 4)] is True             # vt 10: beyond every window


def test_provable_disjointness_excludes_reroute():
    # same shape, but the groups are provably disjoint: everything is forced
    foreign = [_send(4, "b2", 0, 10), _recv(5, "b2", 0, 9)]
    claims = {0: CELL_CLAIMS, 1: [("input", 5), ("output", 4)]}
    f0 = force_group([_cell(), foreign], {}, 0, claims)
    f1 = force_group([_cell(), foreign], {}, 1, claims)
    assert all(f0.values()) and all(f1.values())


def test_constant_pointer_may_alias_a_base():
    # a constant pointer is not provably disjoint from base+offset cells
    const = [_send(4, None, 100, 10), _recv(5, None, 100, 9)]
    claims = {0: CELL_CLAIMS, 1: [("input", 5), ("output", 4)]}
    f1 = force_group([_cell(), const], {0: {1}, 1: {0}}, 1, claims)
    assert f1[("input", 5)] is False             # could read the cell's send


def test_wide_recv_window_not_forced():
    # the interior recv's threshold covers BOTH sends -> two matchings; the
    # greedy pre-solution pairs it with the later send (own-op time here)
    g = [_send(0, "b", 0, 1), _recv(1, "b", 0, 0),
         _send(2, "b", 0, 4), _recv(3, "b", 0, 4)]
    f = force_group([g], {}, 0, {0: [("edge", 3, 2), ("input", 1), ("output", 0)]})
    assert f[("edge", 3, 2)] is False
    assert f[("input", 1)] is True
    assert f[("output", 0)] is False


def test_unbalanced_member_unsatisfiable():
    # one send, two recvs at one cell: at most one input per cell and
    # inputs == outputs leave the second recv nothing to read
    g = [_send(0, "b", 0, 1), _recv(1, "b", 0, 0), _recv(2, "b", 0, 2)]
    with pytest.raises(ValueError, match="no matching at all"):
        force_group([g], {}, 0, {0: []})


def test_cross_check_catches_wrong_presolution():
    # two inputs at one cell can never be a model: the feasibility pass must
    # flag the bogus pre-solution instead of silently "forcing" against it
    with pytest.raises(ValueError, match="cross-check failed"):
        force_group([_cell()], {}, 0, {0: [("input", 1), ("input", 3)]})
