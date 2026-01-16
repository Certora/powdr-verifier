import contextlib
from pathlib import Path
from typing import TextIO, Optional


# make pysmt support Mod
# be careful with the order of the imports

# first patch pysmt.operators
from pysmt import operators
from pysmt.solvers.z3 import Z3Converter, Z3Solver, z3

operators.MOD = operators.ALL_TYPES[-1] + 1
operators.ALL_TYPES.append(operators.MOD)
operators.IRA_OPERATORS = operators.IRA_OPERATORS | frozenset([operators.MOD])
operators.__OP_STR__[operators.MOD] = 'MOD'

# patch logics
from pysmt import logics

logics.PYSMT_LOGICS = logics.PYSMT_LOGICS | frozenset([logics.QF_UFNIA, logics.UFNIA])
Z3Solver.LOGICS = Z3Solver.LOGICS | frozenset([logics.QF_UFNIA, logics.UFNIA])

# then patch all the formula manager and all the walkers
from pysmt.formula import FormulaManager
from pysmt.walkers import IdentityDagWalker
from pysmt.printers import HRPrinter
from pysmt.oracles import AtomsOracle, FreeVarsOracle, QuantifierOracle, TheoryOracle, TypesOracle
from pysmt.type_checker import SimpleTypeChecker

FormulaManager.Mod = lambda self, left, right: self.create_node(node_type=operators.MOD, args=(left, right))

# oracles.py
QuantifierOracle.walk_mod = QuantifierOracle.walk_all
TheoryOracle.walk_mod = TheoryOracle.walk_div
FreeVarsOracle.walk_mod = FreeVarsOracle.walk_simple_args
AtomsOracle.walk_mod = AtomsOracle.walk_theory_op
TypesOracle.walk_mod = TypesOracle.walk_combine
# printers.py
HRPrinter.walk_mod = lambda self, formula: self.walk_nary(formula, '%')
# type_checker.py
SimpleTypeChecker.walk_mod = SimpleTypeChecker.walk_realint_to_realint
# solvers/z3.py
Z3Converter.walk_mod = Z3Converter.make_walk_binary(z3.Z3_mk_mod)
# walkers/identitydag.py
IdentityDagWalker.walk_mod = lambda self, formula, args, **kwargs: self.mgr.Mod(args[0], args[1])

import pysmt.smtlib.printers
# smtlib/printers.py
pysmt.smtlib.printers.SmtPrinter.walk_mod = lambda self, formula: self.walk_nary(formula, 'mod')

# now go on with the rest

from pysmt.fnode import FNode
from pysmt import substituter
from pysmt.logics import Logic
from pysmt.shortcuts import *
from pysmt.smtlib import script, printers
from pysmt.substituter import FunctionInterpretation

from ..utils import ARGS

# make pysmt support QF_UFNIA and UFNIA
UFNIA = logics.UFNIA
QF_UFNIA = logics.QF_UFNIA

def Mod(left, right):
    r""".. math:: l % r """
    return get_env().formula_manager.Mod(left, right)


DEFAULT_SOLVER = 'z3'
cvc5_path = Path('cvc5/build/bin/cvc5')
if cvc5_path.exists():
    get_env().factory.add_generic_solver('cvc5ff',
        [ 'cvc5/build/bin/cvc5', '--mod-range-solver', '--nia-intro-mm-mod' ],
        [ logics.QF_UFNIA, logics.UFNIA ]
    )
    #DEFAULT_SOLVER = 'cvc5ff'

UF_MOD = Symbol('uf_mod', FunctionType(INT, [INT, INT]))
REAL_MOD = Symbol('mod', FunctionType(INT, [INT, INT]))

def wrap_mod(input: FNode, modulus: Optional[FNode] = None) -> FNode:
    if modulus is None:
        modulus = Int(ARGS().field_type.value)
    return Mod(input, modulus)

class SMTPrettyPrinter(script.SmtPrinter):

    COLLAPSIBLE = operators.CONSTANTS | frozenset([operators.SYMBOL])
    INDENT = '    '

    def __init__(self, env=None, depth=0):
        script.SmtPrinter.__init__(self, env)
        self.depth = depth
        self.is_collapsed = False

        self.functions[operators.SYMBOL] = self.wrap_simple_indent(self.walk_symbol)
        self.functions[operators.INT_CONSTANT] = self.wrap_simple_indent(self.walk_int_constant)
        self.functions[operators.REAL_CONSTANT] = self.wrap_simple_indent(self.walk_real_constant)
        self.functions[operators.BOOL_CONSTANT] = self.wrap_simple_indent(self.walk_bool_constant)
        self.functions[operators.BV_CONSTANT] = self.wrap_simple_indent(self.walk_bv_constant)
        self.functions[operators.STR_CONSTANT] = self.wrap_simple_indent(self.walk_str_constant)
    
    def wrap_simple_indent(self, func):
        def wrapped(child: FNode):
            if not self.is_collapsed:
                self.write(self.INDENT * self.depth)
            yield from func(child)
        return wrapped

    def should_collapse(self, formula: FNode) -> bool:
        return any([
            self.is_collapsed,
            self.depth > 10,
            all([ child.node_type() in self.COLLAPSIBLE for child in formula.args() ]),
            len(str(formula)) < 60
        ])
    
    @contextlib.contextmanager
    def collapsed(self):
        before = self.is_collapsed
        self.is_collapsed = True
        yield
        self.is_collapsed = before

    @contextlib.contextmanager
    def indented(self):
        self.depth += 1
        yield
        self.depth -= 1
    
    def indent(self):
        self.write(self.INDENT * self.depth)

    def write_indented(self, *args, **kwargs):
        self.indent()
        self.write(*args, **kwargs)
    
    @printers.write_annotations
    def walk_nary(self, formula, operator):
        if hasattr(formula, 'comment'):
            self.write_indented(f'; {formula.comment}\n')
        if self.should_collapse(formula):
            if not self.is_collapsed:
                self.indent()
            with self.collapsed():
                self.write(f'({operator}')
                for s in formula.args():
                    self.write(' ')
                    yield s
                self.write(')')
        else:
            self.write_indented(f'({operator}\n')
            with self.indented():
                for s in formula.args():
                    yield s
                    self.write('\n')
            self.write_indented(')')
    
    @printers.write_annotations
    def _walk_quantifier(self, operator, formula):
        assert len(formula.quantifier_vars()) > 0
        self.write_indented(f'({operator}\n')
        with self.indented():
            self.write_indented('(\n')

            with self.indented():
                for s in formula.quantifier_vars():
                    self.write_indented('(')
                    with self.collapsed():
                        yield s
                        self.write(f' {s.symbol_type().as_smtlib(False)})\n')

            self.write_indented(')\n')
        with self.indented():
            yield formula.arg(0)
        self.write('\n')
        self.write_indented(')')

def pretty_print_smtlib(smtlib: script.SmtLibScript, file: TextIO):
    printer = SMTPrettyPrinter(file, depth=1)
    for cmd in smtlib.commands:
        match cmd:
            case script.SmtLibCommand(name='assert'):
                file.write(f'({cmd.name}\n')
                printer.printer(cmd.args[0])
                file.write('\n)\n')
            case _:
                cmd.serialize(file, daggify=False)
                file.write('\n')

def convert_to_smt_script(f: FNode, logic: Logic) -> script.SmtLibScript:
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

def print_formula_to_file(f, LOGIC, dump):
    smtlib = convert_to_smt_script(f, LOGIC)
    pretty_print_smtlib(smtlib, dump)
