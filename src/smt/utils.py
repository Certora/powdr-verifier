import functools
import json
import logging
from typing import Any, Iterable
from types import GeneratorType

from ..smt_backends.pysmt import *
from ..utils.profiling import simple_profile

SUPPORTS_COMMENTS = "comment" in FNode.__slots__


def with_comment(f: FNode, comment: str) -> FNode:
    """Set the comment of f to comment."""
    if f is None:
        return None
    if SUPPORTS_COMMENTS:
        setattr(f, "comment", comment)
    return f


def keep_comment(new: FNode, old: FNode) -> FNode:
    """Copy the comment from old to new."""
    if SUPPORTS_COMMENTS and hasattr(old, "comment"):
        setattr(new, "comment", old.comment)
    return new


def attach_comment(comment: str):
    """
    Decorator that attaches a comment to the result of a function.
    The comment string can use all arguments and keyword arguments of the
    function via the format string syntax.
    """

    def inner(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            res = func(*args, **kwargs)
            if res is None:
                return None
            if isinstance(res, GeneratorType):
                return (with_comment(f, comment.format(*args, **kwargs)) for f in res)
            return with_comment(res, comment.format(*args, **kwargs))

        return wrapper

    return inner


def without_trues(fs: Iterable[FNode]) -> Iterable[FNode]:
    """Filter out `None` and trivially-true formulas from an iterable."""
    return filter(lambda x: x is not None and not x.is_true(), fs)


def as_constant(f: FNode) -> Any:
    """Return a Python value for constants, otherwise a stable string representation."""
    if f.is_constant():
        return f.constant_value()
    return str(f)


def to_nice_model(model: Any) -> dict[str, Any]:
    """Convert a solver model into a JSON-friendly dict, optionally stripping symbol prefixes."""
    return {
        str(k): as_constant(v)
        for k, v in sorted(model, key=lambda x: str(x))
        if not v.is_array_value() and not v.is_array_op()
    }


@attach_comment("BASIC RANGE axiom for {0}")
def field_symbol(sym: FNode) -> FNode:
    """Constrain `sym` to lie in the field range (0 ... p-1) for the configured modulus."""
    return And(LE(Int(0), sym), LT(sym, Int(ARGS().field_type.value)))


def MultiArrayType(index, width, value) -> FNode:
    """Construct an `ArrayType` nested `width` times (i.e. a multi-dimensional array type)."""
    if width > 0:
        return ArrayType(index, MultiArrayType(index, width - 1, value))
    return value


class NameOrIdGenerator:
    """Stable naming helper: use symbol/constant names, else assign fresh ids to compound terms."""

    def __init__(self):
        """Initialize an empty mapping from expressions to stable integer ids."""
        self.mapping = {}

    def __call__(self, x: FNode) -> str:
        """Return `str(x)` for symbols/constants, else a stable fresh id for compound terms."""
        if x.is_constant() or x.is_symbol():
            return str(x)
        return self.mapping.setdefault(x, len(self.mapping))


class VarBaseFormulaSelector:
    """Index formulas by free variables to support quick relevance selection (shallow/deep)."""

    def __init__(self, formulae: list[FNode]):
        """Index formulas by free variables to support shallow/deep relevance selection."""
        var_to_formulae = {f: f.get_free_variables() for f in formulae}
        self.lookup = {
            v: frozenset(f for f in var_to_formulae if v in var_to_formulae[f])
            for v in frozenset.union(*var_to_formulae.values())
        }

    def resolve_shallow(self, vars: list[FNode]) -> FNode:
        """Return formulas that mention any of `vars` (one-hop variable-to-formula lookup)."""
        if not vars:
            return frozenset()
        return frozenset.union(*[self.lookup[v] for v in vars])

    def resolve_deep(self, vars: list[FNode]) -> FNode:
        """Return a fixpoint of formulas reachable via shared variables starting from `vars`."""
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
        """Shallow-resolve formulas relevant to the free variables of formulas `fs`."""
        return self.resolve_shallow(
            frozenset.union(*[f.get_free_variables() for f in fs])
        )

    def resolve_deep_for(self, fs: list[FNode]) -> FNode:
        """Deep-resolve formulas relevant to the free variables of formulas `fs`."""
        return self.resolve_deep(frozenset.union(*[f.get_free_variables() for f in fs]))


class GenericInterpreter(FunctionInterpretation):
    """Provides a generic interpreter for an uninterpreted function symbol.
    Supports both evaluation of concrete arguments and symbolic simplification."""

    def __init__(self, fsym, f):
        """Set up the interpreter. `f` can be a simple concrete evaluator, or a pair of a concrete evaluator and a symbolic simplifier."""
        self.fsym = fsym
        if isinstance(f, tuple):
            self.concrete, self.symbolic = f
        elif callable(f):
            self.concrete = f
            self.symbolic = None
        else:
            logging.error(f"can not use {f} as interpreter for {fsym}")

    def interpret(self, env, args: list[FNode]) -> FNode:
        """Interpret on constants, else use symbolic simplification if available, else keep UF call."""
        if all(arg.is_constant() for arg in args):
            return self.concrete(*[arg.constant_value() for arg in args])
        if self.symbolic is not None:
            if res := self.symbolic(*args):
                return res
        return Function(self.fsym, args)


def partial_evaluate(f: FNode, model: dict[str, Any], interpreters):
    """Partially evaluate a formula by substituting model values and UF interpretations. Run up to three iterations."""
    substitutions = {}
    for name, value in model.items():
        if isinstance(value, bool):
            substitutions[Symbol(name, BOOL)] = Bool(value)
        elif isinstance(value, int):
            substitutions[Symbol(name, INT)] = Int(value)
    interpretations = {
        sym: GenericInterpreter(sym, f) for sym, f in interpreters.items()
    }

    last = None
    cnt = 3
    while last != f and cnt > 0 and not f.is_constant():
        last = f
        f = f.substitute(substitutions, interpretations).simplify()
        cnt -= 1
    
    if f.is_int_constant():
        f = Int(f.constant_value() % ARGS().field_type.value)

    return f


def find_unique_solution(s: Solver, f: FNode) -> Optional[dict[str, int]]:
    """Return a unique satisfying assignment for `f` (over its free vars), or None if non-unique/unsat."""
    try:
        s.push()
        s.add_assertion(f)
        if s.solve():
            model = s.get_model()
            vars = f.get_free_variables()
            s.add_assertion(Or(*[Not(Equals(v, c)) for v, c in model if v in vars]))
            res = s.solve()
            s.pop()
            if res:
                return None
            return {v: c for v, c in model if v in vars}

        s.pop()
        return None
    except:
        return None
