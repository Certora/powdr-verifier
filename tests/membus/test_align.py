"""Cross-circuit memory-bus alignment (before/after a removal), AS1."""
import pytest

from src.membus import align


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0 = "from_state__timestamp_0@1"
FS1 = "from_state__timestamp_1@2"
PVA = "rs_aux__base__prev_timestamp_0@7"   # cell 8, access 0 (input recv)
PVB = "rs_aux__base__prev_timestamp_1@8"   # cell 8, access 1 (reads send_a)
PVC = "rs_aux__base__prev_timestamp_0@9"   # cell 12 (input recv)


def _send(ptr, ts):
    return {"id": 1, "mult": 1, "args": [1, ptr, 0, 0, 0, 0, ts]}


def _recv(ptr, ts):
    return {"id": 1, "mult": -1, "args": [1, ptr, 0, 0, 0, 0, ts]}


# before: cell 8 = [send_a@T0(0), recv_a input(1), send_b@T3 out(2), recv_b<-send_a(3)];
#         cell 12 = [send_c@T3 out(4), recv_c input(5)]
def _before():
    return {
        "bus_interactions": [
            _send(8, FS0), _recv(8, PVA), _send(8, FS1), _recv(8, PVB),
            _send(12, FS1), _recv(12, PVC),
        ],
        "constraints": [
            _add(FS0, _m(-1, PVA), -1),
            _add(FS1, _m(-1, PVB), -1),
            _add(FS0, _m(-1, PVC), -1),
            _add(FS1, _m(-1, FS0), -3),
        ],
    }


def _after(keep):
    """after = the before interactions at ordinals in `keep`, plus optional extras."""
    b = _before()["bus_interactions"]
    return {"bus_interactions": [b[i] for i in keep], "constraints": []}


def _row(al, before_id):
    return next(r for r in al.rows if r.before_id == before_id)


def test_removal_maps_kept_and_local_pairs():
    # after removes the interior pair (send_a #0, recv_b #3), keeps the boundary
    al = align.compute(_before(), _after([1, 2, 4, 5]), 1, 1)
    assert al.unique and al.n_kept == 4 and al.n_removed == 2 and al.n_local_pairs == 1
    # kept boundary -> after
    assert _row(al, 1).status == "kept" and _row(al, 1).local_role == "input"
    assert _row(al, 1).after_id is not None
    assert _row(al, 2).status == "kept" and _row(al, 2).local_role == "output"
    # removed interior pair cross-references locally (send_a #0 <-> recv_b #3)
    assert _row(al, 0).status == "removed" and _row(al, 0).local_partners == [3]
    assert _row(al, 3).status == "removed" and _row(al, 3).local_partners == [0]
    assert _row(al, 3).after_id is None


def test_kept_interior_has_both_after_and_local():
    # after keeps EVERYTHING (removed=0): the interior recv_b is kept AND locally
    # connected to send_a (both annotations present).
    al = align.compute(_before(), _after([0, 1, 2, 3, 4, 5]), 1, 1)
    assert al.n_kept == 6 and al.n_removed == 0
    r = _row(al, 3)   # recv_b
    assert r.status == "kept" and r.after_id is not None
    assert r.local_role == "interior" and r.local_partners == [0]


def test_semantic_match_ignores_nonkey_representation():
    # kept interaction with different DATA bytes still matches by (cell, kind, ts)
    after = _after([1, 2, 4, 5])
    after["bus_interactions"][0] = {"id": 1, "mult": -1,
                                    "args": [1, 8, 9, 9, 9, 9, PVA]}   # recv_a, data differs
    al = align.compute(_before(), after, 1, 1)
    assert al.n_kept == 4 and _row(al, 1).status == "kept"


def test_mult0_removed_is_inert():
    before = _before()
    before["bus_interactions"].append({"id": 1, "mult": 0, "args": [1, 8, 0, 0, 0, 0, FS0]})
    al = align.compute(before, _after([1, 2, 4, 5]), 1, 1)   # the mult-0 (#6) is removed
    assert al.n_inert == 1
    assert _row(al, 6).status == "removed" and _row(al, 6).local_role == "inert"
    assert _row(al, 6).local_partners == []


def test_abort_after_not_subset():
    after = _after([1, 2, 4, 5])
    after["bus_interactions"].append(_send(99, FS0))   # after-only interaction
    with pytest.raises(ValueError, match="not present in before"):
        align.compute(_before(), after, 1, 1)


def test_abort_removed_boundary_input():
    # remove the input recv_a (#1) -> a boundary interaction was removed
    with pytest.raises(ValueError, match="boundary input recv"):
        align.compute(_before(), _after([0, 2, 3, 4, 5]), 1, 1)


def test_abort_partner_kept():
    # remove recv_b (#3) but keep its send_a (#0) -> removed set unbalanced
    with pytest.raises(ValueError, match="self-balance"):
        align.compute(_before(), _after([0, 1, 2, 4, 5]), 1, 1)


def test_abort_not_globally_unique():
    # add a 3rd send to cell 8 -> unbalanced cell -> solve not unique -> abort
    before = _before()
    before["bus_interactions"].append(_send(8, [FS1, "+", 1]))
    with pytest.raises(ValueError, match="not globally unique"):
        align.compute(before, before, 1, 1)


def test_abort_symbolic_address_space():
    # a memory interaction with a symbolic AS could be AS1 -> must not be silently dropped
    before = _before()
    before["bus_interactions"].append(
        {"id": 1, "mult": 1, "args": ["mem_as@5", 8, 0, 0, 0, 0, FS0]})
    with pytest.raises(ValueError, match="symbolic address space"):
        align.compute(before, _after([1, 2, 4, 5]), 1, 1)


def test_abort_address_space_not_1():
    with pytest.raises(ValueError, match="only address space 1"):
        align.compute(_before(), _after([1, 2, 4, 5]), 1, 2)


def test_json_schema_stable():
    d = align.compute(_before(), _after([1, 2, 4, 5]), 1, 1).as_dict()
    assert d["address_space"] == 1 and d["unique"] is True
    assert set(d["counts"]) >= {"before", "after", "kept", "removed", "local_pairs", "inert"}
    assert {"before_id", "status", "after_id", "local_role", "local_partners"} <= set(
        d["interactions"][0])
