import contextlib
from datetime import datetime
from io import StringIO
import logging
from pathlib import Path
import re
import semver
import subprocess
from typing import TextIO, Optional


# make pysmt support Mod
# be careful with the order of the imports

# first patch pysmt.operators
from pysmt import operators
from pysmt import walkers
from pysmt.solvers.z3 import Z3Converter, Z3Solver, z3

operators.MOD = operators.ALL_TYPES[-1] + 1
operators.ALL_TYPES.append(operators.MOD)
operators.IRA_OPERATORS = operators.IRA_OPERATORS | frozenset([operators.MOD])
operators.__OP_STR__[operators.MOD] = 'MOD'

# patch logics
from pysmt import logics

# make pysmt support QF_UFNIA and UFNIA
logics.AUFNIA = logics.Logic(name="AUFNIA",
                description=\
"""Closed formulas with free function and predicate symbols over a
theory of arrays of integers.""",
                arrays=True,
                arrays_const=True,
                integer_arithmetic=True,
                real_arithmetic=False,
                linear=False,
                uninterpreted=True)
logics.QF_AUFNIA = logics.Logic(name="QF_AUFNIA",
                  description=\
"""Closed quantifier-free formulas over the theory of integer
arrays extended with free sort and function symbols.""",
                  quantifier_free=True,
                  arrays=True,
                  arrays_const=True,
                  integer_arithmetic=True,
                  linear=False,
                  uninterpreted=True)

UFNIA = logics.UFNIA
QF_UFNIA = logics.QF_UFNIA
AUFNIA = logics.AUFNIA
QF_AUFNIA = logics.QF_AUFNIA

logics.PYSMT_LOGICS = logics.PYSMT_LOGICS | frozenset([logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])
logics.SMTLIB2_LOGICS = logics.SMTLIB2_LOGICS | frozenset([logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])
Z3Solver.LOGICS = Z3Solver.LOGICS | frozenset([logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])

# then patch all the formula manager and all the walkers
from pysmt.formula import FormulaManager
from pysmt.simplifier import Simplifier
from pysmt.walkers import DagWalker, IdentityDagWalker
from pysmt.printers import HRPrinter, SmartPrinter
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
SmartPrinter.walk_mod = SmartPrinter.smart_walk
# simplifier.py
def simplify_mod(self, formula, args, **kwargs):
    """Simplify MOD applications for constant arguments and a few trivial identities."""
    sl, sr = args
    if sl.is_int_constant() and sr.is_int_constant():
        return Int(sl.constant_value() % sr.constant_value())
    if sl.is_zero(): return sl
    return self.manager.Mod(sl, sr)
Simplifier.walk_mod = simplify_mod
# type_checker.py
SimpleTypeChecker.walk_mod = SimpleTypeChecker.walk_realint_to_realint
# solvers/z3.py
Z3Converter.walk_mod = Z3Converter.make_walk_binary(z3.Z3_mk_mod)
# walkers/identitydag.py
IdentityDagWalker.walk_mod = lambda self, formula, args, **kwargs: self.mgr.Mod(args[0], args[1])

import pysmt.smtlib.printers
# smtlib/printers.py
pysmt.smtlib.printers.SmtPrinter.walk_mod = lambda self, formula: self.walk_nary(formula, 'mod')
pysmt.smtlib.printers.SmtDagPrinter.walk_mod = lambda self, formula, args: self.walk_nary(formula, args, 'mod')

from pysmt.fnode import FNode

FNode.is_mod = lambda self: self.node_type() == operators.MOD

# now go on with the rest

from pysmt import substituter
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import Logic
from pysmt.shortcuts import *
from pysmt.smtlib import script, printers
from pysmt.substituter import FunctionInterpretation

from ..utils.args import ARGS

class SimpleSizeOracle(DagWalker):
    """Simple version of SizeOracle that does not throw a warning."""
    def __init__(self, env=None):
        DagWalker.__init__(self, env=env)
    def get_size(self, formula, measure):
        return self.walk(formula)
    @walkers.handles(operators.ALL_TYPES)
    def walk_all(self, formula, args, **kwargs):
        return 1 + sum(args)
get_env()._sizeo = SimpleSizeOracle(get_env())

def Mod(left, right):
    r""".. math:: l % r """
    return get_env().formula_manager.Mod(left, right)

def Equals(left, right):
    assert left.get_type() == right.get_type()
    if left.get_type().is_bool_type():
        return Iff(left, right)
    else:
        return pysmt.shortcuts.Equals(left, right)

solvers = [
    {
        'name': 'cvc5ff',
        'path': Path('~/certora/powdr/cvc5/build/bin/cvc5').expanduser(),
        'options': [ '--incremental', '--produce-models', '--mod-range-solver', '--nia-intro-mm-mod' ],
        'logics': [ logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA ],
    },
    {
        'name': 'z3-latest',
        'path': Path('~/bin/z3-4.15.4').expanduser(),
        'options': ['-smt2', '-in'],
        'logics': logics.SMTLIB2_LOGICS,
        'min-version': ('Z3 version ([0-9.]+)', '4.12.2'),
    }
]

for solver in solvers:
    if not solver['path'].exists():
        logging.warning(f"did not add solver {solver['name']}: {solver['path']} does not exist")
    if 'min-version' in solver:
        res = subprocess.run([solver['path'], '--version'], capture_output=True, text=True)
        version = re.search(solver['min-version'][0], res.stdout).group(1)
        if semver.compare(version, solver['min-version'][1]) < 0:
            logging.warning(f"did not add solver {solver['name']} because it is too old (version {version} < {solver['min-version'][1]})")
            continue
    logging.info(f"adding solver {solver['name']} from {solver['path']}")
    get_env().factory.add_generic_solver(solver['name'],
        [ solver['path'] ] + solver['options'],
        solver['logics'],
    )


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
        self.write_indented(f'({operator}')
        with self.indented():
            if len(formula.quantifier_vars()) < 5:
                self.write(' (')
                with self.collapsed():
                    for s in formula.quantifier_vars():
                        self.write('(')
                        yield s
                        self.write(f' {s.symbol_type().as_smtlib(False)}) ')
                self.write(')\n')
            else:
                self.write('\n')
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

def pretty_print_formula(f: FNode) -> str:
    with StringIO() as s:
        printer = SMTPrettyPrinter(s, depth=1)
        printer.printer(f)
        return s.getvalue()

def script_with_sorted_declarefuns(smtlib: script.SmtLibScript) -> script.SmtLibScript:
    cmds = smtlib.commands
    newcmds = []
    declares = []

    while cmds:
        c = cmds.pop(0)
        match c:
            case script.SmtLibCommand(name='declare-fun'):
                declares.append(c)
            case _:
                newcmds.extend(sorted(declares, key=lambda cmd: cmd.args[0].symbol_name()))
                declares = []
                newcmds.append(c)

    smtlib.commands = newcmds
    return smtlib

def convert_to_smt_script(f: FNode, logic: Logic) -> script.SmtLibScript:
    smtlib = script.smtlibscript_from_formula(f, None)
    smtlib = script_with_sorted_declarefuns(smtlib)

    # add model production and model retrieval
    smtlib.commands.insert(1, script.SmtLibCommand(name='set-option', args=[':produce-models', 'true']))
    smtlib.commands.insert(2, script.SmtLibCommand(name='set-option', args=[':incremental', 'true']))
    smtlib.add_command(script.SmtLibCommand(name='get-model', args=[]))
    return smtlib

def print_formula_to_file(f, LOGIC, dump):
    smtlib = convert_to_smt_script(f, LOGIC)
    smtlib.commands.insert(0, script.SmtLibCommand(name='set-info', args=[':source', f'generated {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}']))
    pretty_print_smtlib(smtlib, dump)

def z3_simplify(f: FNode) -> FNode:
    s = Solver()
    if isinstance(s, Z3Solver):
        simplifier = z3.Tactic('simplify')
        convf = s.converter.convert(f)
        simp = simplifier(convf, elim_and=True, pull_cheap_ite=True, ite_extra_rules=True).as_expr()
        return s.converter.back(simp)
    logging.warning("z3_simplify: not a Z3Solver")
    return None
