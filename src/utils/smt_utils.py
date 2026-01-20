from typing import Any, Iterable

from ..smt_backends.pysmt import *

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

class VarBaseFormulaSelector:
    def __init__(self, formulae: list[FNode]):
        var_to_formulae = { f: f.get_free_variables() for f in formulae }
        self.lookup = {
            v: frozenset(f for f in var_to_formulae if v in var_to_formulae[f])
            for v in frozenset.union(*var_to_formulae.values())
        }
    
    def resolve_shallow(self, vars: list[FNode]) -> FNode:
        if not vars:
            return frozenset()
        return frozenset.union(*[self.lookup[v] for v in vars])

    def resolve_deep(self, vars: list[FNode]) -> FNode:
        if not vars:
            return frozenset()
        last = frozenset()
        cur = self.resolve_shallow(vars)
        while cur != last:
            last = cur
            vars = vars | frozenset.union(*[f.get_free_variables() for f in last])
            cur = self.resolve_shallow(vars)
        return cur

    def resolve_shallow_for(self, fs: list[FNode]) -> FNode:
        return self.resolve_shallow(frozenset.union(*[f.get_free_variables() for f in fs]))
    def resolve_deep_for(self, fs: list[FNode]) -> FNode:
        return self.resolve_deep(frozenset.union(*[f.get_free_variables() for f in fs]))
