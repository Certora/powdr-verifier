from typing import Any, Callable, Iterable


def merge_dicts(obj: Iterable, get_key: Callable[[Any], dict]) -> dict:
    """Merge dictionaries produced by `get_key` for each element in `obj` (later keys win)."""
    res = {}
    for o in obj:
        res.update(get_key(o))
    return res
