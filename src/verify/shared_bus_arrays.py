"""Shared memory-bus array alignment between before/after APC encodings.

Computes structurally identical interaction prefixes/suffixes and emits
``set-info :shared-array-*`` pairs consumed by ``simplify.array_subst``.
"""
import logging

from . import SetInfo
from ..simplify.skolem_utils import emit_pin_setinfo
from ..smt.conversion import SmtConverter
from ..smt.utils import FNode, Equals

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"

SETINFO_SHARED_ARRAYS_PREFIX = ":shared-array-"


def _memory_bus_id(data: dict) -> int | None:
    """Return the numeric bus ID for ``Memory``, or ``None`` if absent."""
    bus_ids = data.get("bus_map", {}).get("bus_ids", {})
    for bid, btype in bus_ids.items():
        if btype == "Memory":
            return int(bid)
    return None


def shared_bus_arrays(
    before_data: dict, after_data: dict,
    before_conv: SmtConverter, after_conv: SmtConverter,
) -> dict[FNode, FNode]:
    """Identify memory bus array symbols that are provably equal across sides.

    The memory bus is encoded as a chain of array variables
    (``memory-0-mult``, ``memory-1-mult``, ..., ``memory-N-mult`` for
    each field), where each step applies a ``Store`` driven by one bus
    interaction.  Both the *before* and *after* converters produce their
    own chain independently, even when many interactions are unchanged
    by the optimization step.

    This function compares the *raw* bus interactions (the JSON
    expressions before SMT conversion) element-by-element.  Because
    both sides use the same variable names (``before-``/``after-``
    prefixes are only added during ``convert_manual``), two raw
    interactions that are equal as JSON values are guaranteed to
    represent the same memory access.

    If the first ``k`` interactions are identical, then the array state
    at steps 0 through ``k`` is the same on both sides — they start
    from equal base arrays (equated by ``build_io_relation``)
    and apply the same sequence of stores.  Similarly, if the last ``m``
    interactions match, the array state converges from the end.

    For each such shared step, every array-typed auxiliary symbol
    (``memory-{step}-mult``, ``memory-{step}-data0``, etc.) is paired
    with its counterpart on the other side.  The resulting map
    ``{before_sym: after_sym}`` is emitted as ``set-info`` annotations
    that the ``array_subst`` simplifier pass later reads and converts
    into ``(assert (= before-X after-X))`` assertions.

    Why only array-typed symbols?
        The intermediate non-array symbols (``-1``, ``-2``, ``-new``
        suffixed ``Int`` variables from ``update_multidim_array``)
        were tested but asserting their equality actually hurts solver
        performance — Z3 handles array equalities far more efficiently
        via its specialized congruence closure than it handles large
        numbers of ``Int`` equality assertions.

    Returns
    -------
    dict[FNode, FNode]
        Map from before-side array symbols to their after-side
        counterparts.  Empty if no interactions match.
    """
    mem_id = _memory_bus_id(before_data)
    if mem_id is None:
        return {}

    before_mem = [
        bi for bi in before_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]
    after_mem = [
        bi for bi in after_data["machine"]["bus_interactions"]
        if bi["id"] == mem_id
    ]

    n = len(before_mem)
    if n != len(after_mem) or n == 0:
        return {}

    prefix_same = 0
    for i in range(n):
        if before_mem[i] != after_mem[i]:
            break
        prefix_same += 1

    suffix_same = 0
    for i in range(1, n + 1):
        if n - i < prefix_same:
            break
        if before_mem[-i] != after_mem[-i]:
            break
        suffix_same += 1

    shared_steps: set[int] = set()
    for i in range(prefix_same + 1):
        shared_steps.add(i)
    for i in range(n - suffix_same, n + 1):
        shared_steps.add(i)

    if not shared_steps:
        return {}

    before_enc = before_conv.bus_interaction_encoder.memory
    after_enc = after_conv.bus_interaction_encoder.memory

    def strip_prefix(name: str) -> str:
        for p in (BEFORE_PREFIX + "-", AFTER_PREFIX + "-"):
            if name.startswith(p):
                return name[len(p):]
        return name

    ba = before_enc.auxiliaries if hasattr(before_enc, 'auxiliaries') else set()
    aa = after_enc.auxiliaries if hasattr(after_enc, 'auxiliaries') else set()

    before_by_suffix: dict[str, FNode] = {}
    for s in ba:
        if s.get_type().is_array_type():
            before_by_suffix[strip_prefix(s.symbol_name())] = s

    subs: dict[FNode, FNode] = {}
    for s in aa:
        if not s.get_type().is_array_type():
            continue
        suffix = strip_prefix(s.symbol_name())
        partner = before_by_suffix.get(suffix)
        if partner is None or partner.get_type() != s.get_type():
            continue
        parts = suffix.split("-")
        if len(parts) >= 2:
            try:
                step = int(parts[1])
            except ValueError:
                continue
            if step in shared_steps:
                subs[partner] = s

    if subs:
        logging.info(
            f"shared bus arrays: {len(subs)} symbols "
            f"(prefix={prefix_same}, suffix={suffix_same}, total={n})"
        )
    return subs


def shared_arrays_setinfo(
    subs: dict[FNode, FNode], *, reverse: bool = False
) -> SetInfo:
    """Emit set-info commands for shared memory bus array equalities.

    ``subs`` maps ``{before_sym: after_sym}``.  For *completeness*
    (after-vars quantified) pass ``reverse=True`` so the pins read
    ``Equals(after, before)``; for *soundness* (before-vars quantified)
    use the default ``reverse=False``.
    """
    prefix = SETINFO_SHARED_ARRAYS_PREFIX[1:]
    if reverse:
        pins = [Equals(v, k) for k, v in subs.items()]
    else:
        pins = [Equals(k, v) for k, v in subs.items()]
    cmds = [emit_pin_setinfo(prefix, i, eq) for i, eq in enumerate(pins)]
    return SetInfo(cmds)
