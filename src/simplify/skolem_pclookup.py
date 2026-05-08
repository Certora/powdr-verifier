"""PC-lookup skolem contributor.

Mirrors :mod:`.skolem_names` and :mod:`.skolem_rules`: not a standalone
simplifier pass, just the :func:`contribute` function used by
:mod:`.skolem` to add pre-resolved pc-lookup pins to a shared
:class:`~.skolem.SkolemMap`.

Why this lives in the simplifier
--------------------------------
The verifier emits one pin per ``find_unique_solution`` hit it could
resolve at encode time, serialized as a ``:skolem-pclookup-N`` set-info
entry whose value is an SMT-LIB ``Equals(var, expr)``. Resolution has
to happen at verifier time because it relies on the encoder's
*incremental* ``constraint_solver`` (where the bus axioms and bool
flag constraints have been accumulated as the encoding was built);
rebuilding an equivalent solver in the simplifier from the post-NNF
formula is too slow for Z3 to make the decisive flag inferences in a
useful time bound.

What this module does
---------------------
* :data:`SETINFO_PREFIX`  - the set-info keyword prefix the verifier
  uses for pc-lookup pins.
* :func:`collect_pins`    - load every ``:skolem-pclookup-N`` value
  back as an ``FNode`` equation.
* :func:`contribute`      - for every loaded equation, pin the qvar
  side on the shared :class:`SkolemMap` if not already pinned.
"""

from ..smt.utils import *

from .skolem_utils import load_setinfo_pins, split_equation


SETINFO_PREFIX = ":skolem-pclookup-"


def collect_pins(smt_script: script.SmtLibScript) -> list:
    """Return the pre-resolved pclookup pins carried by set-info entries."""
    return load_setinfo_pins(smt_script, SETINFO_PREFIX[1:])


def contribute(skolem_map, pclookup: list) -> None:
    """Pin every pre-resolved pclookup equation whose lhs qvar is in the map.

    Each entry is an ``Equals(var, expr)``; we extract the symbol side
    and pin it on the shared :class:`~.skolem.SkolemMap` if not already
    pinned by a more specific contributor (rules / derived). Same shape
    as :func:`.skolem_derived.contribute`, kept separate so the source
    tag (``"pclookup"``) and the verifier-side resolution live next to
    their consumer.
    """
    for eq in pclookup:
        split = split_equation(eq)
        if split is None:
            continue
        var, expr = split
        if var in skolem_map.qvars and not skolem_map.is_pinned(var):
            skolem_map.pin(var, expr, source="pclookup")
