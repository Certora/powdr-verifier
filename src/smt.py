
import collections
import logging
import pprint
from typing import Any
from pysmt import logics
from pysmt.fnode import FNode
from pysmt.shortcuts import *
from pysmt.smtlib import *
from pysmt.typing import *

from .bus_interactions import *
from .utils import map_recursive, ARGS, log_conversion
from .pretty_printer import pretty_print_smtlib
from .rewriter import rewrite
from .smt_utils import wrap_mod

LOGIC = logics.UFNIA


FormulaWithAxioms = collections.namedtuple('FormulaWithAxioms', ['formula', 'axioms', 'derived'])

class SmtConverter:
    def __init__(self):
        self.bus_interaction_encoder = BusInteractionEncoder.get_encoder()
        self.field_symbols = set()
    
    def convert_constraints(self, data: list[Any]) -> Any:
        return And(*[
            Equals(wrap_mod(c), Int(0)) for c in data
        ])
    
    def convert_derived(self, data: list[Any]) -> Any:
        res = []
        for derived in data:
            match derived:
                case [{'name': str(name), 'id': int}, value]:
                    res.append(Equals(Symbol(name, INT), value))
                case _:
                    logging.error(f"Unsupported derived column: {derived}")
        return res

    @log_conversion(level=logging.DEBUG)
    def convert(self, data: Any) -> Any:
        match data:
            case {'Number': int(value)}:
                return Int(value)
            case {'Constant': int(value)}:
                return Int(value)
            case {'Reference': { 'name': str(name), 'id': int() }}:
                sym = Symbol(name, INT)
                self.field_symbols.add(sym)
                return sym
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
            case {'constraints': list(cs), 'bus_interactions': list(bis), 'derived_columns': list(dc), **rest}:
                return {
                    **rest,
                    'constraints': self.convert_constraints(cs),
                    'bus_interactions': And(*[ self.bus_interaction_encoder.encode(bi) for bi in bis ]),
                    'axioms': self.bus_interaction_encoder.get_axioms(),
                    'derived_columns': self.convert_derived(dc),
                }
            case _:
                return None
    
    def convert_recursive(self, data: Any) -> Any:
        return map_recursive(data, self.convert)
    
    def __basic_range_axioms(self) -> list[FNode]:
        return [
            And(
                LE(Int(0), sym),
                LT(sym, Int(ARGS().field_type.value))
            ) for sym in self.field_symbols
        ]

    def to_formula_with_axioms(self, data: Any) -> FormulaWithAxioms:
        data = self.convert_recursive(data)
        return FormulaWithAxioms(
            formula=And(data['machine']['constraints'], data['machine']['bus_interactions']),
            axioms=self.__basic_range_axioms() + data['machine']['axioms'],
            derived=data['machine']['derived_columns'],
        )

def convert_to_smt(data: Any) -> FNode:
    smt_converter = SmtConverter()
    formula = smt_converter.to_formula_with_axioms(data)
    if ARGS().log_smt:
        logging.info(f'after smt conversion:\n{pprint.pformat(formula, width=80)}')
    return formula

def check_formula(f: FNode) -> bool:
    if ARGS().dump_smt:
        with open(get_smt_dump_filename(), 'w') as dump:
            pretty_print_smtlib(f, dump, LOGIC)
    logging.info(f'solving...')
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
