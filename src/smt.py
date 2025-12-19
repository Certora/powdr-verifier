
import collections
import logging
import pprint
from re import L
from typing import Any, Optional
from pysmt import logics
from pysmt.shortcuts import *
from pysmt.typing import *
from pysmt.fnode import FNode
from pysmt.smtlib import *

from .bus_interactions import *
from .utils import map_recursive, args, log_conversion
from .pretty_printer import pretty_print_smtlib

LOGIC = logics.UFNIA


FormulaWithAxioms = collections.namedtuple('FormulaWithAxioms', ['formula', 'axioms'])

class SmtConverter:
    def __init__(self):
        self.bus_interaction_encoder = BusInteractionEncoder.get_encoder()

    @log_conversion(level=logging.DEBUG)
    def convert(self, data: Any) -> Optional[Symbol]:
        match data:
            case {'Number': int(value)}:
                return Int(value)
            case {'Reference': { 'name': str(name), 'id': int() }}:
                return Symbol(name, INT)
            case {'UnaryOperation': { 'expr': expr, 'op': str(op) }}:
                match op:
                    case 'Minus': return Minus(Int(0), expr)
                    case _: return None
            case {'BinaryOperation': { 'left': left, 'right': right, 'op': str(op) }}:
                match op:
                    case 'Add': return Plus(left, right)
                    case 'Sub': return Minus(left, right)
                    case 'Mul': return Times(left, right)
                    case _: return None
            case {'expr': expr, **rest} if rest == {}:
                return expr
            case {'constraints': list(cs), 'bus_interactions': list(bis), **rest}:
                return {
                    **rest,
                    'constraints': And(*[ Equals(c, Int(0)) for c in cs ]),
                    'bus_interactions': And(*[ self.bus_interaction_encoder.encode(bi) for bi in bis ]),
                    'axioms': self.bus_interaction_encoder.get_axioms(),
                }
            case _:
                return None
    
    def convert_recursive(self, data: Any) -> Any:
        return map_recursive(data, self.convert)

    def to_formula_with_axioms(self, data: Any) -> FormulaWithAxioms:
        data = self.convert_recursive(data)
        return FormulaWithAxioms(
            formula=And(data['machine']['constraints'], data['machine']['bus_interactions']),
            axioms=data['machine']['axioms'],
        )

def load_smt_formula(data: Any) -> FNode:
    smt_converter = SmtConverter()
    formula = smt_converter.to_formula_with_axioms(data)
    if args().log_smt:
        logging.info(f'after smt conversion:\n{pprint.pformat(formula, width=80)}')
    return formula

def is_equivalent(f1: FormulaWithAxioms, f2: FormulaWithAxioms) -> bool:
    f = And(
        Not(Iff(f1.formula, f2.formula)),
        And(*set(f1.axioms + f2.axioms)),
    )
    if args().dump_smt:
        with open('dump.smt2', 'w') as dump:
            pretty_print_smtlib(f, dump, LOGIC)
    match is_sat(f, logic=LOGIC):
        case True:
            print("SAT")
            print(get_model(f, logic=LOGIC))
            return False
        case False:
            print("UNSAT")
            return True
        case _:
            print(f"UNKNOWN: {res}")
            return False
