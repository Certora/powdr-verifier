from typing import Any, Iterable, Optional

from .utils import ARGS

from .smt_backends.pysmt import *

UF_MOD = Symbol('uf_mod', FunctionType(INT, [INT, INT]))
REAL_MOD = Symbol('mod', FunctionType(INT, [INT, INT]))

def wrap_mod(input: FNode, modulus: Optional[FNode] = None) -> FNode:
    if modulus is None:
        modulus = Int(ARGS().field_type.value)
    return Function(UF_MOD, [input, modulus])

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

def convert_to_smt_script(f: FNode, logic: logics.Logic) -> script.SmtLibScript:
    smtlib = script.smtlibscript_from_formula(f, logic)

    # replace "declare-fun uf_mod" by "define-fun uf_mod"
    for id,cmd in enumerate(smtlib.commands):
        match cmd:
            case script.SmtLibCommand(name='declare-fun') if cmd.args == [UF_MOD]:
                args = [Symbol('x', INT), Symbol('y', INT)]
                define_fun = script.SmtLibCommand(
                    name='define-fun',
                    args=[UF_MOD, args, INT, Function(REAL_MOD, args)]
                )
                smtlib.commands[id] = define_fun
            case _:
                pass

    # add model production and model retrieval
    smtlib.commands.insert(1, script.SmtLibCommand(name='set-option', args=[':produce-models', 'true']))
    smtlib.commands.insert(2, script.SmtLibCommand(name='set-option', args=[':incremental', 'true']))
    smtlib.add_command(script.SmtLibCommand(name='get-model', args=[]))
    return smtlib