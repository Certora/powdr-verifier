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


def contribute(skolem_map, declared: dict[str, FNode]) -> None:
    """Pin same-name witnesses on ``skolem_map`` for every unpinned qvar
    that has a typed same-name match at script scope.

    See the module docstring for the full description.

    Soundness note
    --------------
    Adding ``q := other`` here is a Skolem witness for the existential
    inside the surrounding ``∀ q. body(q)``. After ``simplify_lift_forall``
    collapses the universal to ``body(other)`` the result is strictly
    weaker than the original ∀-formula. That is:

    * sound for **unsat-proving** (an unsat result on the pinned formula
      implies unsat on the original), and
    * incomplete: if ``other`` is the "wrong" witness for some assignment
      of the formula's free variables, the simplifier returns **sat**.

    For the verifier's equivalence-proving use case the trade-off is the
    right one: dissolving the quantifier unlocks downstream simplifications
    (``z3-propagate-values``, ``flatten_outer_array``, ``bounds``, …) that
    are otherwise blocked behind universal scopes. A spurious sat
    surfaces as a tool-reported counterexample which the user can verify
    or reject against the actual circuit traces.

    Previously this contributor was restricted to "program-variable"
    names (those carrying an ``@index`` suffix), which excluded memory
    state qvars like ``after-memory-N-hadinput``. The restriction is
    removed — any qvar with a typed same-name match is now pinned.
    """
    for q in skolem_map.qvars:
        if skolem_map.is_pinned(q):
            continue
        other = declared.get(_strip_prefix(q.symbol_name()))
        if other is None or other == q or other in skolem_map.qvars:
            continue
        if q.get_type() != other.get_type():
            continue
        skolem_map.pin(q, other, source="names")
