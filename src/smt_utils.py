from typing import Any, Iterable, Optional

from .utils import ARGS

from .smt_backends.pysmt import *

def with_comment(f: FNode, comment: str) -> FNode:
    setattr(f, 'comment', comment)
    return f
def keep_comment(new: FNode, old: FNode) -> FNode:
    if hasattr(old, 'comment'):
        setattr(new, 'comment', old.comment)
    return new

def without_trues(fs: Iterable[FNode]) -> Iterable[FNode]:
    return filter(lambda x: not x.is_true(), fs)

def as_constant(f: FNode) -> Any:
    if f.is_constant():
        return f.constant_value()
    return str(f)

def to_nice_model(model: Any) -> dict[str, Any]:
    return {
        str(k): as_constant(v) for k,v in sorted(model, key=lambda x: str(x))
    }

class NameOrIdGenerator:
    def __init__(self):
        self.mapping = {}
    
    def __call__(self, x: FNode) -> str:
        if x.is_constant() or x.is_symbol():
            return str(x)
        return self.mapping.setdefault(x, len(self.mapping))
