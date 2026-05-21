"""Generic decorators (e.g. conditional no-op) and dict merge helpers for encoders."""
from functools import wraps
from typing import Any, Callable, Iterable


def none_if(pred: Callable[[], bool]):
    """Decorator: skip calling ``fn`` when ``pred()`` is true (returns ``None``)."""
    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        @wraps(fn)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            if pred():
                return None
            return fn(*args, **kwargs)

        return wrapper

    return decorator


def s2range(s: str) -> range:
    """Parse ``a:b`` or single index slice strings into a Python ``range`` (open-ended ``b`` allowed)."""
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
