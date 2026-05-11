"""Same-name skolem contributor.

This module is *not* a standalone simplifier pass anymore; it provides
the :func:`contribute` function used by :mod:`.skolem` to populate a
shared :class:`~.skolem.SkolemMap` with same-name witnesses.

For every qvar ``q`` of the current forall, the contributor:

* Strips the ``before-`` / ``after-`` prefix from ``q``'s symbol name.
* Looks up another script-level declared symbol ``q'`` with the same
  stripped name.
* If ``q'`` exists, ``q`` is not also a qvar of this forall, ``q`` is
  not already pinned by a more specific contributor (rules / derived /
  pclookup), and ``q`` and ``q'`` agree on type, pins ``q := q'`` on the
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
    """Return True for program variables (column names with ``@index`` suffix).

    Bus-interaction encoding variables (e.g. ``memory-0-data0``) must not
    be matched by name because their numeric indices do not correspond
    across sides when the number of interactions changes.
    """
    return "@" in _strip_prefix(name)


def contribute(skolem_map, declared: dict[str, FNode]) -> None:
    """Pin same-name witnesses on ``skolem_map`` for unpinned qvars.

    See the module docstring for the full description.
    Only matches program variables (names containing ``@``), not
    bus-interaction encoding variables.
    """
    for q in skolem_map.qvars:
        if skolem_map.is_pinned(q):
            continue
        if not _is_program_variable(q.symbol_name()):
            continue
        other = declared.get(_strip_prefix(q.symbol_name()))
        if other is None or other == q or other in skolem_map.qvars:
            continue
        if q.get_type() != other.get_type():
            continue
        skolem_map.pin(q, other, source="names")
