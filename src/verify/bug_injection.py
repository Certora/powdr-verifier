import copy
import logging
import random
import secrets
from typing import Any, Callable

from ..utils.args import ARGS

logger = logging.getLogger(__name__)

Injector = Callable[[random.Random, dict[str, Any]], None]

_VAR_NAMES = []


_OPS = frozenset({"+", "-", "*"})


def _vars_in_expr(expr: Any) -> set[str]:
    if isinstance(expr, str):
        return {expr}
    if isinstance(expr, list):
        if len(expr) == 3 and isinstance(expr[1], str) and expr[1] in _OPS:
            return _vars_in_expr(expr[0]) | _vars_in_expr(expr[2])
        if len(expr) == 2 and expr[0] == "-":
            return _vars_in_expr(expr[1])
        return set().union(*(_vars_in_expr(x) for x in expr))
    if isinstance(expr, dict):
        return set().union(*(_vars_in_expr(v) for v in expr.values()))
    return set()


def _var_names_from_target(target: dict[str, Any]) -> set[str]:
    m = target["machine"]
    names: set[str] = set()
    for c in m["constraints"]:
        names |= _vars_in_expr(c)
    for bi in m["bus_interactions"]:
        names |= _vars_in_expr(bi)
    for dc in m["derived_columns"]:
        names |= _vars_in_expr(dc)
    names |= _vars_in_expr(target["subs"])
    names |= _vars_in_expr(target["optimistic_constraints"])
    return names


def _load_var_names(target: dict[str, Any]) -> None:
    global _VAR_NAMES
    _VAR_NAMES = list(_var_names_from_target(target))


def _int_literal_sites(expr: Any) -> list[tuple[list[Any], int]]:
    out: list[tuple[list[Any], int]] = []
    if isinstance(expr, list):
        for i, x in enumerate(expr):
            if isinstance(x, int):
                out.append((expr, i))
            else:
                out.extend(_int_literal_sites(x))
    elif isinstance(expr, dict):
        for v in expr.values():
            out.extend(_int_literal_sites(v))
    return out


def _expr_child_refs(node: Any) -> list[tuple[Any, Any]]:
    if isinstance(node, list):
        if len(node) == 3 and isinstance(node[1], str) and node[1] in _OPS:
            return [(node, 0), (node, 2)]
        if len(node) == 2 and node[0] == "-":
            return [(node, 1)]
        return [(node, i) for i in range(len(node))]
    if isinstance(node, dict):
        return [(node, k) for k in node]
    return []


def _random_expr_slot(rng: random.Random, node: Any, parent: Any, key: Any) -> tuple[Any, Any]:
    children = _expr_child_refs(node)
    if not children:
        return parent, key
    if rng.getrandbits(1):
        return parent, key
    p2, k2 = rng.choice(children)
    return _random_expr_slot(rng, p2[k2], p2, k2)


def _instructions(target: dict[str, Any]) -> list[Any]:
    b = target["block"]
    if "blocks" in b:
        return b["blocks"][0]["instructions"]
    return b["instructions"]


def inject_add_constraint(rng: random.Random, target: dict[str, Any]) -> None:
    cs = target["machine"]["constraints"]
    match rng.choice(("lit0", "lit1", "var", "minus_c", "minus_xy")):
        case "lit0":
            cs.append(0)
        case "lit1":
            cs.append(1)
        case "var":
            v = rng.choice(_VAR_NAMES)
            cs.append(v)
        case "minus_c":
            x = rng.choice(_VAR_NAMES)
            c = rng.randint(-1000, 1000) % ARGS().field_type.value
            cs.append([x, "-", c])
        case "minus_xy":
            x, y = rng.sample(_VAR_NAMES, 2)
            cs.append([x, "-", y])
    logger.warning("inject add_constraint: %r", cs[-1])


def inject_modify_constraint(rng: random.Random, target: dict[str, Any]) -> None:
    cs = target["machine"]["constraints"]
    i = rng.randrange(len(cs))
    parent, key = _random_expr_slot(rng, cs[i], cs, i)
    old = cs[i]
    match rng.randint(0, 2):
        case 0:
            parent[key] = 0
        case 1:
            parent[key] = 1
        case 2:
            parent[key] = rng.choice(_VAR_NAMES)
    logger.warning("inject modify_constraint %i: %r -> %r", i, old, cs[i])


def inject_remove_constraint(rng: random.Random, target: dict[str, Any]) -> None:
    cs = target["machine"]["constraints"]
    if cs:
        i = rng.randrange(len(cs))
        del cs[i]
        logger.warning("inject remove_constraint: removed %s", i)


def inject_modify_bus_interaction(rng: random.Random, target: dict[str, Any]) -> None:
    bis = target["machine"]["bus_interactions"]
    if not bis:
        return
    idx, bi = rng.choice(list(enumerate(bis)))
    candidates: list[Any] = [bi["mult"], *bi["args"]]
    for expr in candidates:
        sites = _int_literal_sites(expr)
        if sites:
            parent, j = rng.choice(sites)
            old = parent[j]
            parent[j] = old + rng.choice((1, -1))
            logger.warning(
                "inject modify_bus_interaction: interaction[%s] int %s -> %s",
                idx,
                old,
                parent[j],
            )
            return
    if isinstance(bi["id"], int):
        old = bi["id"]
        bi["id"] = old + 1
        logger.warning(
            "inject modify_bus_interaction: interaction[%s] id %s -> %s",
            idx,
            old,
            bi["id"],
        )
    else:
        logger.warning(
            "inject modify_bus_interaction: interaction[%s] skipped (no int literal, id not int)",
            idx,
        )


_EXEC_OR_MEM_BUS_TYPES = frozenset({"ExecutionBridge", "Memory"})


def _bus_type_for_interaction_id(target: dict[str, Any], interaction_id: int) -> Any | None:
    return str(target["bus_map"]["bus_ids"].get(str(interaction_id)))


def inject_remove_bus_interaction(rng: random.Random, target: dict[str, Any]) -> None:
    bis = target["machine"]["bus_interactions"]
    n = len(bis)
    if n == 0:
        return
    i = rng.randrange(n)
    bid = bis[i]["id"]
    btype = _bus_type_for_interaction_id(target, bid)
    logger.warning("inject remove_bus_interaction: bus id %s type %r", bid, btype)
    also_next = (
        btype in _EXEC_OR_MEM_BUS_TYPES
        and rng.getrandbits(1)
        and i + 1 < n
        and bis[i + 1]["id"] == bid
    )
    if also_next:
        del bis[i : i + 2]
        logger.warning(
            "inject remove_bus_interaction: removed indices %s,%s (bus id %s type %s, pair)",
            i,
            i + 1,
            bid,
            btype,
        )
    else:
        del bis[i]
        logger.warning(
            "inject remove_bus_interaction: removed index %s (bus id %s type %s, single)",
            i,
            bid,
            btype,
        )


def inject_modify_instruction(rng: random.Random, target: dict[str, Any]) -> None:
    ins = _instructions(target)
    if not ins:
        return
    ii = rng.randrange(len(ins))
    instr = ins[ii]
    if not isinstance(instr, list) or not instr:
        logger.warning(
            "inject modify_instruction: skipped instructions[%s] not a non-empty list",
            ii,
        )
        return
    j = rng.randrange(len(instr))
    if isinstance(instr[j], int):
        old = instr[j]
        instr[j] = old + rng.choice((1, -1))
        logger.warning(
            "inject modify_instruction: instructions[%s][%s] int %s -> %s",
            ii,
            j,
            old,
            instr[j],
        )
    else:
        logger.warning(
            "inject modify_instruction: skipped instructions[%s][%s] not int (%r)",
            ii,
            j,
            instr[j],
        )


def inject_remove_instruction(rng: random.Random, target: dict[str, Any]) -> None:
    ins = _instructions(target)
    if len(ins) >= 2:
        i = rng.randrange(len(ins))
        del ins[i]
        logger.warning("inject remove_instruction: removed instructions[%s]", i)


def inject_swap_instructions(rng: random.Random, target: dict[str, Any]) -> None:
    ins = _instructions(target)
    if len(ins) >= 2:
        i, j = rng.sample(range(len(ins)), 2)
        ins[i], ins[j] = ins[j], ins[i]
        logger.warning("inject swap_instructions: swapped instructions[%s] <-> instructions[%s]", i, j)


def inject_remove_derived_column(rng: random.Random, target: dict[str, Any]) -> None:
    dcs = target["machine"]["derived_columns"]
    if dcs:
        i = rng.randrange(len(dcs))
        del dcs[i]
        logger.warning("inject remove_derived_column: removed derived_columns[%s]", i)


_INJECTORS: tuple[Injector, ...] = (
    inject_add_constraint,
    inject_modify_constraint,
    inject_remove_constraint,
    inject_modify_bus_interaction,
    inject_remove_bus_interaction,
    inject_modify_instruction,
    inject_remove_instruction,
    inject_swap_instructions,
    inject_remove_derived_column,
)


_INSTRUCTION_BLOCK_SYNC = frozenset(
    {
        inject_modify_instruction,
        inject_remove_instruction,
        inject_swap_instructions,
    }
)


def apply_injection(before: dict[str, Any], after: dict[str, Any]) -> None:
    raw = ARGS().inject
    if raw is None:
        return
    seed = secrets.randbelow(1 << 20) if raw == "random" else int(raw)
    rng = random.Random(seed)
    target = before if rng.getrandbits(1) else after
    _load_var_names(target)
    side = "before" if target is before else "after"
    fn = rng.choice(_INJECTORS)
    logger.warning("injecting bug on %s with %s [seed=%s]", side, fn.__name__, seed)
    fn(rng, target)
    if fn in _INSTRUCTION_BLOCK_SYNC:
        other = after if target is before else before
        other["block"] = copy.deepcopy(target["block"])
        logger.warning(
            "inject: copied block from %s to the other dump (%s)",
            side,
            fn.__name__,
        )
