import contextlib
from datetime import datetime
from io import StringIO
import logging
from pathlib import Path
import re
import semver
import subprocess
from typing import TextIO, Optional

from pysmt import operators
from pysmt import substituter

@substituter.handles(set(operators.ALL_TYPES) - operators.QUANTIFIERS - {operators.FUNCTION})
def __new_compute_node_result(self, formula, *args, **kwargs):
    self.__original_compute_node_result(formula, *args, **kwargs)
    if hasattr(formula, "comment"):
        if memoized := self.memoization.get(self._get_key(formula, **kwargs), None):
             setattr(memoized, "comment", formula.comment)
substituter.MGSubstituter.__original_compute_node_result = substituter.MGSubstituter._compute_node_result
substituter.MGSubstituter._compute_node_result = __new_compute_node_result

# make pysmt support Mod
# be careful with the order of the imports

# first patch pysmt.operators
from pysmt import walkers
from pysmt.solvers.z3 import Z3Converter, Z3Solver, z3

operators.MOD = operators.ALL_TYPES[-1] + 1
operators.ALL_TYPES.append(operators.MOD)
operators.IRA_OPERATORS = operators.IRA_OPERATORS | frozenset([operators.MOD])
operators.__OP_STR__[operators.MOD] = 'MOD'

# patch logics
from pysmt import logics

# make pysmt support QF_UFNIA and UFNIA
logics.ALL = logics.Logic(name="ALL",
                description="Everything.",
                arrays=True,
                arrays_const=True,
                integer_arithmetic=True,
                real_arithmetic=True,
                linear=True,
                uninterpreted=True)
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
ALL = logics.ALL

logics.PYSMT_LOGICS = logics.PYSMT_LOGICS | frozenset([logics.ALL, logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])
logics.SMTLIB2_LOGICS = logics.SMTLIB2_LOGICS | frozenset([logics.ALL, logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])
logics.LOGICS = logics.LOGICS | frozenset([logics.ALL, logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])
Z3Solver.LOGICS = Z3Solver.LOGICS | frozenset([logics.ALL, logics.QF_UFNIA, logics.UFNIA, logics.QF_AUFNIA, logics.AUFNIA])

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
def __z3converter_init(self, env, z3_ctx):
    self.__old__init__(env, z3_ctx)
    self._back_fun[z3.Z3_OP_MOD] = lambda args, expr: self.mgr.Mod(args[0], args[1])
Z3Converter.__old__init__ = Z3Converter.__init__
Z3Converter.__init__ = __z3converter_init
Z3Converter.walk_mod = Z3Converter.make_walk_binary(z3.Z3_mk_mod)

# walkers/identitydag.py
IdentityDagWalker.walk_mod = lambda self, formula, args, **kwargs: self.mgr.Mod(args[0], args[1])

from pysmt.smtlib import printers, commands, script
# smtlib/printers.py
printers.SmtPrinter.walk_mod = lambda self, formula: self.walk_nary(formula, 'mod')
printers.SmtDagPrinter.walk_mod = lambda self, formula, args: self.walk_nary(formula, args, 'mod')

from pysmt.fnode import FNode

FNode.is_mod = lambda self: self.node_type() == operators.MOD
FNode.__str__ = lambda self: self.serialize()

from pysmt.smtlib.parser import SmtLibParser as OriginalSmtLibParser

class SmtLibParser(OriginalSmtLibParser):
    def __init__(self, *args, **kwargs):
        OriginalSmtLibParser.__init__(self, *args, **kwargs)
        self.interpreted["mod"] = self._operator_adapter(self.env.formula_manager.Mod)
        self.interpreted["mod_total"] = self._operator_adapter(self.env.formula_manager.Mod)

def __serialize_command(self, outstream=None, printer=None, daggify=True):
    if self.name == 'echo':
        outstream.write(f"({self.name} {self.args[0]})")
    elif self.name == commands.CHECK_SAT_ASSUMING:
        outstream.write("(%s" % self.name)
        for a in self.args:
            outstream.write(" (")
            printer.printer(a)
            outstream.write(")")
        outstream.write(")")
    else:
        self.super_serialize(outstream, printer, daggify)

script.SmtLibCommand.super_serialize = script.SmtLibCommand.serialize
script.SmtLibCommand.serialize = __serialize_command

# now go on with the rest

from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import Logic
from pysmt.shortcuts import *
from pysmt.smtlib import script, printers, solver
from pysmt.substituter import FunctionInterpretation, MGSubstituter, handles
from pysmt.utils import quote
from ..utils.args import ARGS

def __ensure_leading_colon(name: str) -> str:
    return f":{name.removeprefix(':')}"

pysmt.smtlib.solver.SmtLibSolver.declare_fun = lambda self, symbol: self._declare_variable(symbol)
pysmt.smtlib.solver.SmtLibSolver.assert_ = lambda self, formula: self.add_assertion(formula)
pysmt.smtlib.solver.SmtLibSolver.set_info = lambda self, name, value: \
    self._send_silent_command(script.SmtLibCommand(name=commands.SET_INFO, args=[__ensure_leading_colon(name), value]))
pysmt.smtlib.solver.SmtLibSolver.set_option = lambda self, name, value: \
    self._send_silent_command(script.SmtLibCommand(name=commands.SET_OPTION, args=[__ensure_leading_colon(name), value]))
pysmt.smtlib.solver.SmtLibSolver.check_sat = lambda self: self.solve()

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
        logging.info(f"did not add solver {solver['name']}: {solver['path']} does not exist")
    if 'min-version' in solver:
        res = subprocess.run([solver['path'], '--version'], capture_output=True, text=True)
        version = re.search(solver['min-version'][0], res.stdout).group(1)
        if semver.compare(version, solver['min-version'][1]) < 0:
            logging.info(f"did not add solver {solver['name']} because it is too old (version {version} < {solver['min-version'][1]})")
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

    def __init__(self, env=None, depth=0, in_script=False):
        script.SmtPrinter.__init__(self, env)
        self.depth = depth
        self.is_collapsed = False
        self.in_script = in_script

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
    
    def write_if_collapsed(self, ifs, elses):
        if self.is_collapsed:
            self.write(ifs)
        else:
            self.write(elses)

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
    
    def printer(self, f):
        if self.in_script:
            if self.should_collapse(f):
                super().printer(f)
            else:
                self.write('\n')
                with self.indented():
                    super().printer(f)
                self.write('\n')
        else:
            super().printer(f)


    @printers.write_annotations
    def walk_nary(self, formula, operator):
        if hasattr(formula, 'comment') and not self.is_collapsed:
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
        if hasattr(formula, 'comment'):
            self.write_indented(f'; {formula.comment}\n')
        assert len(formula.quantifier_vars()) > 0
        self.write_indented(f'({operator}')
        with self.indented():
            if len(str(formula.quantifier_vars())) < 50:
                self.write(' (')
                with self.collapsed():
                    for s in sorted(formula.quantifier_vars(), key=str):
                        self.write('(')
                        yield s
                        self.write(f' {s.symbol_type().as_smtlib(False)}) ')
                self.write(')\n')
            else:
                self.write('\n')
                self.write_indented('(\n')
                with self.indented():
                    for s in sorted(formula.quantifier_vars(), key=str):
                        self.write_indented('(')
                        with self.collapsed():
                            yield s
                            self.write(f' {s.symbol_type().as_smtlib(False)})\n')
                self.write_indented(')\n')
        with self.indented():
            yield formula.arg(0)
        self.write('\n')
        self.write_indented(')')

    @printers.write_annotations
    def walk_array_value(self, formula):
        if not self.is_collapsed:
            self.write_indented('')
        assign = formula.array_value_assigned_values_map()
        for _ in range(len(assign)):
            self.write("(store ")

        self.write("((as const %s)" % formula.get_type().as_smtlib(False))
        self.write_if_collapsed(" ", "\n")
        with self.indented():
            yield formula.array_value_default()
            self.write_if_collapsed(" ", "\n")
        if not self.is_collapsed:
            self.indent()
        self.write(")")

        for k in sorted(assign, key=str):
            self.write(" ")
            yield k
            self.write(" ")
            yield assign[k]
            self.write(")")

def pretty_print_smtlib(smtlib: script.SmtLibScript, file: TextIO):
    printer = SMTPrettyPrinter(file, in_script=True)
    for cmd in smtlib.commands:
        cmd.serialize(file, printer=printer, daggify=False)
        file.write('\n')

def pretty_print_formula(f: FNode) -> str:
    with StringIO() as s:
        printer = SMTPrettyPrinter(s)
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

def convert_to_smt_script(f: FNode, status = None) -> script.SmtLibScript:
    smtlib = script.smtlibscript_from_formula(f, None)
    smtlib = script_with_sorted_declarefuns(smtlib)

    smtlib.commands[0].args[0] = "ALL"

    smtlib.commands.insert(0, script.SmtLibCommand(name='set-info', args=[':source', f'generated {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}']))
    # add model production and model retrieval
    smtlib.commands.insert(2, script.SmtLibCommand(name='set-option', args=[':produce-models', 'true']))
    smtlib.commands.insert(3, script.SmtLibCommand(name='set-option', args=[':produce-unsat-cores', 'true']))
    if status is not None:
        smtlib.commands.insert(4, script.SmtLibCommand(name='set-info', args=[':status', status]))
    #smtlib.commands.insert(2, script.SmtLibCommand(name='set-option', args=[':incremental', 'true']))
    # proof logging
    #smtlib.commands.insert(4, script.SmtLibCommand(name='set-option', args=[':solver.proof.log', 'proof-log.smt2']))
    #smtlib.commands.insert(5, script.SmtLibCommand(name='set-option', args=[':sat.euf', 'true']))
    # get model and unsat cores
    #smtlib.add_command(script.SmtLibCommand(name='get-info', args=[':reason-unknown']))
    smtlib.add_command(script.SmtLibCommand(name='get-model', args=[]))
    smtlib.add_command(script.SmtLibCommand(name='get-unsat-core', args=[]))
    return smtlib

def print_formula_to_file(f, dump):
    smtlib = convert_to_smt_script(f)
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
