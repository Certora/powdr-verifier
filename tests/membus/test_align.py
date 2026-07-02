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
#         cell 12 = [send_c@T+4 out(4), recv_c input(5)]
# (every op has its own timestamp, as in real dumps — the match is ts-based)
def _before():
    return {
        "bus_interactions": [
            _send(8, FS0), _recv(8, PVA), _send(8, FS1), _recv(8, PVB),
            _send(12, [FS1, "+", 1]), _recv(12, PVC),
        ],
        "constraints": [
            _add(FS0, _m(-1, PVA), -1),
            _add(FS1, _m(-1, PVB), -1),
            _add(FS0, _m(-1, PVC), -1),
            _add(FS1, _m(-1, FS0), -3),
        ],
    }


def _after(keep):
    """after = the before interactions at ordinals in `keep` (keeps the R1/R2
    constraints so send_offsets(after) resolves, as in real dumps)."""
    b = _before()
    return {"bus_interactions": [b["bus_interactions"][i] for i in keep],
            "constraints": b["constraints"]}


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
    # an after-only interaction at a timestamp before never used
    after["bus_interactions"].append(_send(99, [FS1, "+", 7]))
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
    before["bus_interactions"].append(_send(8, [FS1, "+", 2]))
    with pytest.raises(ValueError, match="not globally unique"):
        align.compute(before, before, 1, 1)


def test_matches_across_send_timestamp_rewrite():
    # inlining rewrites a send's ts (`fs1` -> `fs0 + 3`, same virtual time) but not the
    # recv's prev_timestamp. align must still match via the vtime tier (no solve on after).
    fs0, fs1 = "from_state__timestamp_0@1", "from_state__timestamp_1@2"
    pv = "aux__base__prev_timestamp_0@7"
    r1 = _add(fs1, _m(-1, fs0), -3)          # fs1 = fs0 + 3
    r2 = _add(fs0, _m(-1, pv), -1)           # recv bound
    before = {"bus_interactions": [_recv(8, pv), _send(8, fs1)], "constraints": [r1, r2]}
    after = {"bus_interactions": [_recv(8, pv), _send(8, [fs0, "+", 3])],  # send ts rewritten
             "constraints": [r2]}            # no R1 (inlined single base)
    al = align.compute(before, after, 1, 1)
    assert al.n_kept == 2 and al.n_removed == 0 and al.unique   # matched despite rewrite


def test_matches_final_apc_is_valid_gating():
    # the final exported APC gates every mult by ±is_valid; align matches it to the
    # ±1 predecessor by normalizing the kind (assume is_valid==1), same as solve.
    b = _before()
    iv = "is_valid@99"
    after = {"bus_interactions": [{"id": 1, "mult": iv if x["mult"] == 1 else ["-", iv],
                                   "args": x["args"]} for x in b["bus_interactions"]],
             "constraints": b["constraints"]}
    al = align.compute(b, after, 1, 1)                      # default assume_is_valid=True
    assert al.n_kept == 6 and al.n_removed == 0 and al.unique


def test_abort_symbolic_multiplicity():
    # a genuinely symbolic mult (not ±is_valid) — pre-solver — is not solved form
    b = _before()
    b["bus_interactions"].append(
        {"id": 1, "mult": ["opcode@5", "*", "is_valid@6"], "args": [1, 8, 0, 0, 0, 0, FS0]})
    with pytest.raises(ValueError, match="symbolic multiplicity"):
        align.compute(b, _after([1, 2, 4, 5]), 1, 1)


def test_abort_symbolic_address_space():
    # a memory interaction with a symbolic AS could be AS1 -> must not be silently dropped
    before = _before()
    before["bus_interactions"].append(
        {"id": 1, "mult": 1, "args": ["mem_as@5", 8, 0, 0, 0, 0, FS0]})
    with pytest.raises(ValueError, match="symbolic address space"):
        align.compute(before, _after([1, 2, 4, 5]), 1, 1)


def test_abort_unsupported_address_space():
    with pytest.raises(ValueError, match="unsupported address space"):
        align.compute(_before(), _after([1, 2, 4, 5]), 1, 3)


# --------------------------------------------------------------------------- #
# AS2: cross-match only (purely ts-based; no solve, no local connections)
# --------------------------------------------------------------------------- #

LIM0 = "mem_ptr_limbs__0_0@20"
LIM1 = "mem_ptr_limbs__1_0@21"
PV2 = "write_base_aux__prev_timestamp_0@22"


def _as2(mult, ptr, ts):
    return {"id": 1, "mult": mult, "args": [2, ptr, 0, 0, 0, 0, ts]}


def _before_as2():
    ptr = _add(LIM0, _m(65536, LIM1))
    return {
        "bus_interactions": [_as2(-1, ptr, PV2), _as2(1, ptr, [FS0, "+", 1])],
        "constraints": [_add(FS0, _m(-1, PV2), -1)],
    }


def test_as2_pure_kept_matches_despite_pointer_rewrite():
    # a pass re-associates / substitutes the pointer expression but keeps the ts:
    # the match is purely ts-based, so the pair still aligns as fully kept.
    before = _before_as2()
    rewritten = _add(_m(65536, LIM1), "mem_ptr_limbs__0_9@77")   # reassoc + limb subst
    after = {"bus_interactions": [_as2(-1, rewritten, PV2),
                                  _as2(1, rewritten, [FS0, "+", 1])],
             "constraints": before["constraints"]}
    al = align.compute(before, after, 1, 2)
    assert al.n_kept == 2 and al.n_removed == 0 and al.unique
    assert _row(al, 0).after_id == 0 and _row(al, 1).after_id == 1
    assert _row(al, 0).local_role == "" and _row(al, 0).local_partners == []


def test_as2_removal_aborts_without_solve():
    before = _before_as2()
    after = {"bus_interactions": [before["bus_interactions"][0]],
             "constraints": before["constraints"]}
    with pytest.raises(ValueError, match="requires solve"):
        align.compute(before, after, 1, 2)


def test_as2_removed_mult0_is_inert():
    before = _before_as2()
    before["bus_interactions"].append(_as2(0, _add(LIM0, _m(65536, LIM1)), FS1))
    after = {"bus_interactions": before["bus_interactions"][:2],
             "constraints": before["constraints"]}
    al = align.compute(before, after, 1, 2)
    assert al.n_kept == 2 and al.n_removed == 1 and al.n_inert == 1
    assert _row(al, 2).local_role == "inert"


def test_as2_ambiguous_timestamp_aborts():
    # two before interactions sharing (kind, ts) cannot be told apart
    before = _before_as2()
    other_ptr = _add("mem_ptr_limbs__0_5@50", _m(65536, "mem_ptr_limbs__1_5@51"))
    before["bus_interactions"].append(_as2(1, other_ptr, [FS0, "+", 1]))  # same ts as #1
    with pytest.raises(ValueError, match="ambiguous before"):
        align.compute(before, before, 1, 2)


def test_json_schema_stable():
    d = align.compute(_before(), _after([1, 2, 4, 5]), 1, 1).as_dict()
    assert d["address_space"] == 1 and d["unique"] is True
    assert set(d["counts"]) >= {"before", "after", "kept", "removed", "local_pairs", "inert"}
    assert {"before_id", "status", "after_id", "local_role", "local_partners"} <= set(
        d["interactions"][0])
