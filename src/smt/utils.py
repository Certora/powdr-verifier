import logging
from typing import Any, Iterable

from ..smt_backends.pysmt import *

SUPPORTS_COMMENTS = 'comment' in FNode.__slots__

def with_comment(f: FNode, comment: str) -> FNode:
    if SUPPORTS_COMMENTS:
        setattr(f, 'comment', comment)
    return f
def keep_comment(new: FNode, old: FNode) -> FNode:
    if SUPPORTS_COMMENTS and hasattr(old, 'comment'):
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
        str(k): as_constant(v)
        for k,v in sorted(model, key=lambda x: str(x))
        if not v.is_array_value() and not v.is_array_op()
    }

def MultiArrayType(index, width, value) -> FNode:
    if width > 0:
        return ArrayType(index, MultiArrayType(index, width-1, value))
    return value

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

def check_formula(f: FNode) -> bool:
    if ARGS().dump_smt:
        with open(ARGS().smt_dump_filename, 'w') as dump:
            print_formula_to_file(f, UFNIA, dump)

    logging.debug(f"checking formula with logic {UFNIA} and solver {ARGS().solver}")
    s = Solver(logic=UFNIA, name=ARGS().solver, solver_options={'timeout': 60000})
    s.add_assertion(f)
    try:
        match s.solve():
            case True:
                return True, s.get_model()
            case False:
                return False, None
            case _:
                return None, None
    except SolverReturnedUnknownResultError:
        return None, None

class GenericInterpreter(FunctionInterpretation):
    def __init__(self, fsym, f):
        self.fsym = fsym
        if isinstance(f, tuple):
            self.concrete, self.symbolic = f
        elif callable(f):
            self.concrete = f
            self.symbolic = None
        else:
            logging.error(f"can not use {f} as interpreter for {fsym}")

    def interpret(self, env, args: list[FNode]) -> FNode:
        if all(arg.is_constant() for arg in args):
            return self.concrete(*[arg.constant_value() for arg in args])
        if self.symbolic is not None:
            if res := self.symbolic(*args):
                return res
        return Function(self.fsym, args)

def partial_evaluate(f: FNode, model: dict[str, int], bi):
    substitutions = {
        Symbol(name, INT): Int(value) for name, value in model.items()
    }
    interpretations = {
        sym: GenericInterpreter(sym, f)
        for sym, f in bi.get_interpreters().items()
    }

    last = None
    cnt = 3
    while last != f and cnt > 0 and not f.is_constant():
        last = f
        f = f.substitute(substitutions, interpretations).simplify()
        cnt -= 1
    return f
