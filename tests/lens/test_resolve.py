"""Filename resolution from (group, block, step)."""
import json

import pytest

from src.lens import resolve
from src.lens.resolve import ResolveError


def _make_dumps(tmp_path):
    group = tmp_path / "guest-keccak"
    group.mkdir()
    steps = [
        (0, "unopt"), (11, "memory"), (16, "remove_free"),
        (22, "memory"), (33, "memory"),
    ]
    for nnn, name in steps:
        f = group / f"apc_candidate_111_{nnn:03d}_{name}.json"
        f.write_text(json.dumps({"constraints": [], "bus_interactions": []}))
    # decoy: a different candidate id should be ignored by index_block
    (group / "apc_candidate_222_011_memory.json").write_text("{}")
    return tmp_path


def test_group_dir_variants(tmp_path):
    _make_dumps(tmp_path)
    assert resolve.group_dir("keccak", tmp_path).name == "guest-keccak"
    assert resolve.group_dir("guest-keccak", tmp_path).name == "guest-keccak"
    with pytest.raises(ResolveError):
        resolve.group_dir("nope", tmp_path)


def test_normalize_block():
    assert resolve.normalize_block("apc_candidate_2103924") == "2103924"
    assert resolve.normalize_block("2103924") == "2103924"


def test_index_block_sorted_and_scoped(tmp_path):
    _make_dumps(tmp_path)
    d = resolve.group_dir("keccak", tmp_path)
    entries = resolve.index_block(d, "111")
    assert [e.nnn for e in entries] == [0, 11, 16, 22, 33]  # decoy 222 excluded
    with pytest.raises(ResolveError):
        resolve.index_block(d, "999")


def test_index_block_includes_bare_nnn_final(tmp_path):
    # the final compaction dump has no _<pass> suffix (..._051.json); it must
    # still be indexed. _substitutions.json (no numeric NNN) must not.
    group = tmp_path / "guest-keccak"
    group.mkdir()
    (group / "apc_candidate_111_000_unopt.json").write_text("{}")
    (group / "apc_candidate_111_051.json").write_text("{}")
    (group / "apc_candidate_111_substitutions.json").write_text("[]")
    entries = resolve.index_block(resolve.group_dir("keccak", tmp_path), "111")
    assert [e.nnn for e in entries] == [0, 51]
    bare = entries[1]
    assert bare.pass_name == "" and bare.label == "051"
    # resolvable by its NNN
    assert resolve.resolve_step(entries, "51").label == "051"


def test_resolve_step_int_and_base(tmp_path):
    _make_dumps(tmp_path)
    d = resolve.group_dir("keccak", tmp_path)
    entries = resolve.index_block(d, "111")
    assert resolve.resolve_step(entries, "11").pass_name == "memory"
    assert resolve.resolve_step(entries, "016").pass_name == "remove_free"
    assert resolve.resolve_step(entries, "unopt").nnn == 0
    assert resolve.resolve_step(entries, "base").nnn == 0


def test_resolve_step_pass_name_ambiguity(tmp_path):
    _make_dumps(tmp_path)
    d = resolve.group_dir("keccak", tmp_path)
    entries = resolve.index_block(d, "111")
    assert resolve.resolve_step(entries, "remove_free").nnn == 16  # unique name
    with pytest.raises(ResolveError, match="ambiguous"):
        resolve.resolve_step(entries, "memory")
    assert resolve.resolve_step(entries, "memory@2").nnn == 22
    assert resolve.resolve_step(entries, "memory#3").nnn == 33
    with pytest.raises(ResolveError):
        resolve.resolve_step(entries, "memory@9")
    with pytest.raises(ResolveError):
        resolve.resolve_step(entries, "nope")
