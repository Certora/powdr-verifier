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


def detect_format(data: dict[str, Any]) -> str:
    """Classify a dump as ``circuit`` or ``constraints`` (powdr's two types).

    - ``circuit``: the ``Apc``/``SymbolicMachine`` form (``AlgebraicExpression``,
      with a unary ``["-", e]`` and a real ``-`` operator). Emitted as the
      ``_000_unopt`` base dump; identified by the ``block``/``subs`` keys.
    - ``constraints``: the ``ConstraintSystem`` form (``GroupedExpression`` =
      quadratic/linear/constant), emitted after each optimizer pass. Only
      ``+``/``*`` appear; subtraction is lowered to ``+ (p-1)*x``.
    """
    if "block" in data or "subs" in data:
        return "circuit"
    if "constraints" in data:
        return "constraints"
    return "unknown"


def machine_of(data: dict[str, Any]) -> dict[str, Any]:
    """Return the machine sub-tree (constraints / bus_interactions / derived).

    A per-step dump *is* the machine (has top-level ``constraints``); a base
    ``_000_unopt`` dump nests it under ``machine``.
    """
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
