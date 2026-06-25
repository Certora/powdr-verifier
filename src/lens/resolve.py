"""Resolve dump filenames from ``(group, block, step)``.

The dump directory holds ``apc_candidate_<id>_<NNN>_<pass>.json`` files. The
``NNN`` indices are contiguous from ``000`` per candidate, but the
``NNN -> pass`` mapping varies between candidate variants and pass names
repeat within a candidate (``memory`` at 011, 022, 033). So we always scan
the directory and resolve against what is actually present rather than
assuming a fixed step table.
"""
import re
from dataclasses import dataclass
from pathlib import Path

DEFAULT_ROOT = Path("powdr-dumps")
_NAME_RE = re.compile(r"apc_candidate_(\d+)_(\d+)_(.+)\.json$")
_BASE_PASSES = {"unopt", "base"}


class ResolveError(Exception):
    """Raised when a group / block / step cannot be resolved to a file."""


@dataclass(frozen=True)
class StepEntry:
    """One dump file for a block, parsed from its filename."""

    nnn: int
    pass_name: str
    path: Path

    @property
    def label(self) -> str:
        return f"{self.nnn:03d}_{self.pass_name}"


def normalize_block(block: str) -> str:
    """Return the bare numeric candidate id (strip any ``apc_candidate_``)."""
    m = re.search(r"(\d+)", block)
    if not m:
        raise ResolveError(f"block {block!r} has no candidate id digits")
    return m.group(1)


def group_dir(group: str, root: Path | None = None) -> Path:
    """Resolve a group name to its dump directory.

    Accepts a plain group (``keccak`` -> ``<root>/guest-keccak``), an
    already-prefixed group (``guest-keccak``), or a path to an existing dir.
    """
    root = root or DEFAULT_ROOT
    candidates = [Path(group), root / group, root / f"guest-{group}"]
    for cand in candidates:
        if cand.is_dir():
            return cand
    tried = ", ".join(str(c) for c in candidates)
    raise ResolveError(f"group {group!r} not found (tried: {tried})")


def sole_group_dir(root: Path | None = None) -> Path:
    """Return the only group dir under ``root``; error if 0 or >1 exist."""
    root = root or DEFAULT_ROOT
    dirs = sorted(p for p in root.iterdir() if p.is_dir()) if root.is_dir() else []
    if len(dirs) == 1:
        return dirs[0]
    if not dirs:
        raise ResolveError(f"no group directories under {root}")
    names = ", ".join(d.name for d in dirs)
    raise ResolveError(f"multiple groups under {root} ({names}); specify one")


def index_block(directory: Path, block: str) -> list[StepEntry]:
    """Return all step entries for ``block`` in ``directory``, sorted by NNN."""
    bid = normalize_block(block)
    entries: list[StepEntry] = []
    for path in directory.glob(f"apc_candidate_{bid}_*.json"):
        m = _NAME_RE.match(path.name)
        if m and m.group(1) == bid:
            entries.append(StepEntry(int(m.group(2)), m.group(3), path))
    if not entries:
        raise ResolveError(
            f"no dumps for block {bid} in {directory} "
            f"(expected apc_candidate_{bid}_*.json)"
        )
    return sorted(entries, key=lambda e: e.nnn)


def list_blocks(directory: Path) -> list[str]:
    """Distinct candidate ids present in ``directory``, sorted numerically."""
    ids: set[str] = set()
    for path in directory.glob("apc_candidate_*.json"):
        m = _NAME_RE.match(path.name)
        if m:
            ids.add(m.group(1))
    return sorted(ids, key=int)


def resolve_step(entries: list[StepEntry], step: str) -> StepEntry:
    """Resolve a step token against a block's entries.

    ``step`` is one of: an integer NNN (``11``/``011``); a pass name
    (``memory``), optionally with a 1-based occurrence suffix (``memory@2``
    or ``memory#2``) when the name repeats; or ``unopt``/``base`` for the
    ``000`` base dump.
    """
    token = step.strip()

    # base aliases
    if token.lower() in _BASE_PASSES:
        for e in entries:
            if e.nnn == 0:
                return e
        raise ResolveError("no base (000) dump found")

    # integer NNN
    if token.isdigit():
        nnn = int(token)
        for e in entries:
            if e.nnn == nnn:
                return e
        avail = ", ".join(f"{e.nnn:03d}" for e in entries)
        raise ResolveError(f"step {nnn:03d} not found (have: {avail})")

    # pass name, optional @k / #k occurrence
    occ = None
    m = re.match(r"(.+?)[@#](\d+)$", token)
    if m:
        token, occ = m.group(1), int(m.group(2))
    matches = [e for e in entries if e.pass_name == token]
    if not matches:
        names = ", ".join(sorted({e.pass_name for e in entries}))
        raise ResolveError(f"pass {token!r} not found (have: {names})")
    if occ is not None:
        if not 1 <= occ <= len(matches):
            raise ResolveError(
                f"pass {token!r} has {len(matches)} occurrence(s); "
                f"asked for #{occ}"
            )
        return matches[occ - 1]
    if len(matches) > 1:
        where = ", ".join(f"{e.nnn:03d}" for e in matches)
        raise ResolveError(
            f"pass {token!r} is ambiguous: occurs at {where}. "
            f"Use {token}@N (1-based) or the NNN index."
        )
    return matches[0]


def base_dump_path(directory: Path, block: str) -> Path | None:
    """Path to the block's ``*_000_unopt.json`` base dump (carries bus_map)."""
    bid = normalize_block(block)
    cand = directory / f"apc_candidate_{bid}_000_unopt.json"
    return cand if cand.is_file() else None


def resolve(group: str, block: str, step: str, root: Path | None = None) -> StepEntry:
    """Convenience: resolve a single ``(group, block, step)`` to a StepEntry."""
    directory = group_dir(group, root)
    return resolve_step(index_block(directory, block), step)
