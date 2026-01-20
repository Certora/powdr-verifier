
import collections
import logging
import pprint
from typing import Any, Iterable

from .. import bus_interactions
from .basic_block import BasicBlock
from .args import ARGS, BusInteractionHandlers
from .smt_utils import *

LOGIC = UFNIA

FormulaWithAxioms = collections.namedtuple('FormulaWithAxioms', ['constraints', 'bus_interactions', 'axioms', 'derived', 'globals'])

class SmtConverter:
    def __init__(self, name: str, basic_block: BasicBlock):
        self.basic_block = basic_block
        self.field_symbols = set()
        self.constraints = []
        self.derived_columns = []

        match ARGS().bus_interaction_handler:
            case BusInteractionHandlers.OPENVM:
                self.bus_interaction_encoder = bus_interactions.OpenVMBusInteractionEncoder(basic_block, self)
            case _:
                logging.error(f"Unsupported bus interaction handler: {ARGS().bus_interaction_handler}")
                self.bus_interaction_encoder = None

    def __add_constraint(self, c: FNode, comment: str):
        self.constraints.append(with_comment(c, comment))
    
    def convert_constraints(self, data: Iterable[Any]):
        for id,c in enumerate(data):
            self.__add_constraint(
                Equals(wrap_mod(c), Int(0)),
                f"CONSTRAINT #{id}"
            )
    
    def convert_derived(self, data: Iterable[Any]):
        for derived in data:
            name, value = derived
            match value:
                case {'Constant': int(value)}:
                    self.derived_columns.append(
                        with_comment(
                            Equals(Symbol(name, INT), Int(value)),
                            f"DERIVED COLUMN {name} = {value}"
                        )
                    )
                case _:
                    logging.error(f"Unsupported derived column: {derived}")

    def convert_manual(self, data: Any) -> Any:
        match data:
            # general json structure
            case {
                'block': block,
                'machine': {
                    'constraints': list(cs),
                    'bus_interactions': list(bis),
                    'derived_columns': list(dcs),
                    **rest_machine,
                },
                'subs': subs,
                'optimistic_constraints': _,
                **rest_apc,
            }:
                assert not rest_machine
                assert not rest_apc
                self.convert_constraints(self.convert_manual(c) for c in cs)
                self.bus_interaction_encoder.add_all(self.convert_manual(bi) for bi in bis)
                self.convert_derived(dcs)

            # expressions
            case { 'expr': expr, **rest }:
                assert rest == {}
                return self.convert_manual(expr)
            case [left, '+', right]: return Plus(self.convert_manual(left), self.convert_manual(right))
            case [left, '-', right]: return Minus(self.convert_manual(left), self.convert_manual(right))
            case [left, '*', right]: return Times(self.convert_manual(left), self.convert_manual(right))
            case ['-', right]: return Minus(Int(0), self.convert_manual(right))
            case int(value): return Int(value)
            case str(var):
                sym = Symbol(var, INT)
                self.field_symbols.add(sym)
                return sym

            # bus interactions
            case {'id': int(id), 'mult': mult, 'args': list(args)}:
                return {
                    'id': id,
                    'mult': self.convert_manual(mult),
                    'args': [ self.convert_manual(arg) for arg in args ],
                }

            case _:
                logging.error(f"Unsupported data in conversion: {data}")
    
    def __add_basic_range_axioms(self) -> list[FNode]:
        for sym in sorted(self.field_symbols, key=lambda x: str(x)):
            self.__add_constraint(
                And(
                    LE(Int(0), sym),
                    LT(sym, Int(ARGS().field_type.value))
                ),
                f"BASIC RANGE axiom for {sym}"
            )

    def to_formula_with_axioms(self, data: Any) -> FormulaWithAxioms:
        self.convert_manual(data)
        self.__add_basic_range_axioms()
        bus_interactions = self.bus_interaction_encoder.encode_all()
        return FormulaWithAxioms(
            constraints=self.constraints,
            bus_interactions=bus_interactions,
            axioms=self.bus_interaction_encoder.get_axioms(),
            derived=self.derived_columns,
            globals=self.bus_interaction_encoder.get_globals(),
        )

def convert_to_smt_formula(name: str, data: Any, basic_block: BasicBlock) -> FormulaWithAxioms:
    smt_converter = SmtConverter(name, basic_block)
    formula = smt_converter.to_formula_with_axioms(data)
    if ARGS().log_smt:
        logging.info(f'after smt conversion:\n{pprint.pformat(formula, width=80)}')
    return formula

def check_formula(f: FNode) -> bool:
    if ARGS().dump_smt:
        with open(ARGS().smt_dump_filename, 'w') as dump:
            print_formula_to_file(f, LOGIC, dump)

    s = Solver(logic=LOGIC, name=DEFAULT_SOLVER)
    s.add_assertion(f)
    match s.solve():
        case True:
            print("SAT")
            return s.get_model()
        case False:
            print("UNSAT")
            return False
        case _:
            print(f"UNKNOWN")
            return None
