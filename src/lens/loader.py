"""Load APC dump JSON and resolve bus-id labels.

We use plain ``json.load`` rather than ``src.utils.io.load_json``: the dumps
carry no ``__Path``/``__Action`` markers, and the latter pulls in the global
``ARGS`` machinery and ``Action`` — keeping lens standalone is worth the few
lines.
"""
import json
from pathlib import Path
from typing import Any


def load(path: Path) -> dict[str, Any]:
    """Load a dump JSON file."""
    with open(path) as f:
        return json.load(f)


_FIELD_PRIME = 2013265921  # BabyBear
_HALF = _FIELD_PRIME // 2


def _expr_has_minus(node: Any) -> bool:
    """True if a ``-`` operator (unary or infix) appears anywhere in the tree."""
    if isinstance(node, list):
        for i in range(1, len(node), 2):
            if node[i] == "-":
                return True
        if node and node[0] == "-":  # unary prefix ["-", e]
            return True
        return any(_expr_has_minus(x) for x in node)
    return False


def _expr_has_residue(node: Any) -> bool:
    """True if an upper-half field residue (a grouped-encoding negative) appears."""
    if isinstance(node, bool):
        return False
    if isinstance(node, int):
        return _HALF < node < _FIELD_PRIME
    if isinstance(node, list):
        return any(_expr_has_residue(x) for x in node)
    return False


def detect_format(data: Any) -> str:
    """Classify a dump as ``machine`` / ``constraints`` / ``substitutions``.

    powdr emits three artifacts:
    - ``machine``: ``SymbolicMachine`` / ``AlgebraicExpression`` — uses the
      ``-`` operator (unary ``["-", c]`` / infix ``[a,"-",b]``); negatives are
      signed. This is the ``_000_unopt`` base dump (also has ``block``/``subs``)
      AND the "outer" steps (``loop_iteration``, ``inlining``,
      ``range_constraints``, post-inline ``rule_based``/``trivial_simp``).
    - ``constraints``: ``ConstraintSystem`` / ``GroupedExpression`` — NO ``-``;
      negatives are field residues (``2013265920`` = p−1). The "inner" passes.
    - ``substitutions``: the ``_substitutions.json`` artifact, a top-level list
      of ``[var, definition]`` pairs.

    Discriminator for a bare step dump: ``GroupedExpression`` never emits ``-``,
    so any ``-`` operator ⇒ ``machine``; otherwise an upper-half residue ⇒
    ``constraints``. With no negatives at all the two encodings are identical,
    so we default to ``constraints``.
    """
    if isinstance(data, list):
        return "substitutions"
    if not isinstance(data, dict):
        return "unknown"
    if "block" in data or "subs" in data:
        return "machine"  # apc base dump (algebraic encoding, with context)
    machine = machine_of(data)
    exprs = list(machine.get("constraints", []))
    for bi in machine.get("bus_interactions", []):
        exprs.append(bi.get("mult"))
        exprs.extend(bi.get("args", []))
    if any(_expr_has_minus(e) for e in exprs):
        return "machine"
    if "constraints" in data:
        return "constraints"
    return "unknown"


def machine_of(data: Any) -> dict[str, Any]:
    """Return the machine sub-tree (constraints / bus_interactions / derived).

    A per-step dump *is* the machine (has top-level ``constraints``); a base
    ``_000_unopt`` dump nests it under ``machine``. A substitutions list (or any
    non-dict) has no machine, so return an empty dict.
    """
    if not isinstance(data, dict):
        return {}
    if "constraints" in data:
        return data
    if "machine" in data:
        return data["machine"]
    return data


def bus_label(v: Any) -> str:
    """Flatten a bus_map entry (str | {"Other": ...}) to a readable name."""
    if isinstance(v, str):
        return v
    if isinstance(v, dict):
        _, inner = next(iter(v.items()))  # unwrap "Other"
        if isinstance(inner, str):
            return inner
        if isinstance(inner, dict):
            k, val = next(iter(inner.items()))
            return f"{k}{val}" if not isinstance(val, dict) else k
        return str(inner)
    return str(v)


def load_bus_map(base_path: Path | None) -> dict[str, str]:
    """Return ``{bus_id: label}`` from a base dump, or empty if unavailable."""
    if base_path is None or not base_path.is_file():
        return {}
    data = load(base_path)
    bus_ids = data.get("bus_map", {}).get("bus_ids", {})
    return {str(k): bus_label(v) for k, v in bus_ids.items()}
