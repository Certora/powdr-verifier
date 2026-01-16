
import collections
import logging
import pprint
from typing import Any

from . import bus_interactions
from .basic_block import BasicBlock
from .utils import get_smt_dump_filename, map_recursive, ARGS, log_conversion, BusInteractionHandlers
from .pretty_printer import pretty_print_smtlib
from .rewriter import rewrite
from .smt_utils import *

LOGIC = logics.UFNIA

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

    def __add_constraint(self, c: FNode, comment: str) -> None:
        self.constraints.append(with_comment(c, comment))
    
    def convert_constraints(self, data: list[Any]) -> Any:
        for id,c in enumerate(data):
            self.__add_constraint(
                Equals(wrap_mod(c), Int(0)),
                f"CONSTRAINT #{id}"
            )
    
    def convert_derived(self, data: list[Any]) -> Any:
        for derived in data:
            match derived:
                case [{'name': str(name), 'id': int}, value]:
                    self.derived_columns.append(
                        with_comment(
                            Equals(Symbol(name, INT), value),
                            f"DERIVED COLUMN {name} = {value}"
                        )
                    )
                case _:
                    logging.error(f"Unsupported derived column: {derived}")

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
            case {'constraints': list(cs), 'bus_interactions': list(bis), 'derived_columns': list(dc)}:
                self.convert_constraints(cs)
                self.convert_derived(dc)
                self.bus_interaction_encoder.add_all(bis)
                return data
            case _:
                return None
    
    def convert_recursive(self, data: Any) -> Any:
        return map_recursive(data, self.convert)
    
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
        self.convert_recursive(data)
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
    smtlib.add_command(script.SmtLibCommand(name='get-model', args=[]))
    return smtlib

def check_formula(f: FNode) -> bool:
    if ARGS().dump_smt:
        with open(get_smt_dump_filename(), 'w') as dump:
            smtlib = convert_to_smt_script(f, LOGIC)
            pretty_print_smtlib(smtlib, dump)
    match is_sat(f, logic=LOGIC, solver_name=DEFAULT_SOLVER):
        case True:
            print("SAT")
            return get_model(f, logic=LOGIC, solver_name=DEFAULT_SOLVER)
        case False:
            print("UNSAT")
            return False
        case _:
            print(f"UNKNOWN")
            return None
