
import contextlib
from pysmt import operators
from pysmt.fnode import FNode
from pysmt.shortcuts import *
from pysmt.smtlib import *
from typing import TextIO

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
