from typing import Any, Callable, Iterable

def merge_dicts(obj: Iterable, get_key: Callable[[Any], dict]) -> dict:
    res = {}
    for o in obj:
        res.update(get_key(o))
    return res
