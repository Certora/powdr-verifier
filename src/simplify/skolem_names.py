"""Same-name skolem contributor.

This module is *not* a standalone simplifier pass anymore; it provides
the :func:`contribute` function used by :mod:`.skolem` to populate a
shared :class:`~.skolem.SkolemMap` with same-name witnesses.

For every qvar ``q`` of the current forall, the contributor:

* Strips the ``before-`` / ``after-`` prefix from ``q``'s symbol name.
* Looks up another script-level declared symbol ``q'`` with the same
  stripped name.
* If ``q'`` exists, ``q`` is not also a qvar of this forall, ``q`` is
  not already pinned by a more specific contributor (rules / derived),
  and ``q`` and ``q'`` agree on type, pins ``q := q'`` on the
  :class:`SkolemMap`.

This replaces ``ModelMapBuilder.__heuristic_same_name`` which used to
build the same-name pins as part of the verifier-side encoding ``map``.
The semantics is identical (a same-name fallback for everything not
otherwise pinned), but the data flows through the shared skolem map so
contributors do not have to ``-grep`` the body for existing skolem
equalities.
"""

from ..smt.utils import *


def _strip_prefix(name: str) -> str:
    """Strip the verifier's ``before-``/``after-`` symbol prefix, if present."""
    for prefix in ("before-", "after-"):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def collect_declared_symbols(smt_script: script.SmtLibScript) -> dict[str, FNode]:
    """Return ``{stripped_name: symbol}`` for every ``declare-fun`` in the script.

    Later declarations win on collisions (the encoder never declares two
    ``before-X`` or two ``after-X`` symbols with the same stripped name
    in practice).
    """
    out: dict[str, FNode] = {}
    for cmd in smt_script:
        if cmd.name != "declare-fun":
            continue
        sym = cmd.args[0]
        if not sym.is_symbol():
            continue
        out[_strip_prefix(sym.symbol_name())] = sym
    return out


def _is_program_variable(name: str) -> bool:
    """Return True for program variables (column names with ``@index`` suffix)."""
    return "@" in _strip_prefix(name)


def _is_diff_gadget_column(name: str) -> bool:
    """True for OpenVM LessThan-gadget columns (``diff_marker__*`` / ``diff_val_*``)."""
    stripped = _strip_prefix(name)
    return stripped.startswith("diff_marker") or stripped.startswith("diff_val")


def contribute(skolem_map, declared: dict[str, FNode]) -> None:
    """Pin same-name witnesses on ``skolem_map`` for unpinned qvars.

    See the module docstring for the full description.
    """
    for q in skolem_map.qvars:
        if skolem_map.is_pinned(q):
            continue
        if _is_diff_gadget_column(q.symbol_name()):
            # diff_marker / diff_val are OpenVM LessThan-gadget columns. A
            # same-name `before := after` pin is unsound for them (see
            # skolem_rules module docstring): when the gadget's defining
            # constraints survive on one side only, the after-side value is an
            # arbitrary witness, not the one the before side forces. They must
            # be witnessed by skolem_rules (gadget present) or, when powdr has
            # reduced them to a free range-checked cluster, by the closed-island
            # skolem_isolate pass. Claiming a marker here would also break that
            # island for the sibling diff_val. See journal 2026-06-09.
            continue
        other = declared.get(_strip_prefix(q.symbol_name()))
        if other is None or other == q or other in skolem_map.qvars:
            continue
        if q.get_type() != other.get_type():
            continue
        if not _is_program_variable(q.symbol_name()):
            continue
        skolem_map.pin(q, other, source="names")
