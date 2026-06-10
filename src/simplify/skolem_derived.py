"""Derived / substitution skolem contributor.

Mirrors :mod:`.skolem_names`: not a
standalone simplifier pass, just the :func:`contribute` function used
by :mod:`.skolem` to add derived-column / substitution pins to a shared
:class:`~.skolem.SkolemMap`.

What this module does
---------------------
* :func:`contribute`      - for every loaded equation, pin the qvar
  side on the shared :class:`SkolemMap` if not already pinned.
"""

from ..smt.utils import *

from .skolem_utils import split_equation


def contribute(skolem_map, pins) -> None:
    """Pin every loaded equation whose lhs qvar is in the map.

    Each entry is ``Equals(var, expr)`` or ``Iff(var, expr)``. We only
    pin the side that happens to be a qvar of the current forall; the rest is
    left for other contributors / lift to handle.
    """
    for pin in pins.equations:
        split = split_equation(pin.node)
        if split is None:
            continue
        var, expr = split
        if var in skolem_map.qvars and not skolem_map.is_pinned(var):
            skolem_map.pin(var, expr, source=str(pin.pin_type))
