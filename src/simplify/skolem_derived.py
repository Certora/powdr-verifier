"""Derived / substitution skolem contributor.

Mirrors :mod:`.skolem_names`: not a
standalone simplifier pass, just the :func:`contribute` function used
by :mod:`.skolem` to add derived-column / substitution pins to a shared
:class:`~.skolem.SkolemMap`.

What this module does
---------------------
* :data:`SETINFO_PREFIX`  - the set-info keyword prefix the verifier
  uses for derived / substitution pins (``after_smt.derived`` columns
  for completeness, ``before_conv.convert_substitutions(...)`` for
  soundness).
* :func:`collect_pins`    - load every ``:skolem-derived-N`` value
  back as an ``FNode`` equation (column-derived, substitution, and
  verifier memory-bus alignment pins share this prefix with disjoint indices).
* :func:`contribute`      - for every loaded equation, pin the qvar
  side on the shared :class:`SkolemMap` if not already pinned.
"""

from ..smt.utils import *

from .skolem_utils import load_setinfo_pins, split_equation


SETINFO_PREFIX = ":skolem-derived-"


def collect_pins(smt_script: script.SmtLibScript) -> list:
    """Return the derived / substitution pins carried by set-info entries."""
    return load_setinfo_pins(smt_script, SETINFO_PREFIX[1:])


def contribute(skolem_map, derived: list) -> None:
    """Pin every derived equation whose lhs qvar is in the map.

    Each entry is ``Equals(var, expr)`` or ``Iff(var, expr)``. We only
    pin the side that happens to be a qvar of the current forall; the rest is
    left for other contributors / lift to handle.
    """
    for eq in derived:
        split = split_equation(eq)
        if split is None:
            continue
        var, expr = split
        if var in skolem_map.qvars and not skolem_map.is_pinned(var):
            skolem_map.pin(var, expr, source="derived")
