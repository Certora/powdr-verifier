from typing import Any, Callable, Iterable


def s2range(s: str) -> range:
    match s.split(":", maxsplit=1):
        case [a, b]:
            return range(0 if a == "" else int(a), 2**32 if b == "" else int(b))
        case [index]:
            return range(int(index), int(index)+1)
        case _:
            raise ValueError(f"invalid slice: {s}")


def merge_dicts(obj: Iterable, get_key: Callable[[Any], dict]) -> dict:
    """Merge dictionaries produced by `get_key` for each element in `obj` (later keys win)."""
    res = {}
    for o in obj:
        res.update(get_key(o))
    return res
