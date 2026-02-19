import collections
import logging
import pprint
from typing import Any, Iterable


from .. import bus_interactions
from ..rewriter import rewrite
from ..utils.basic_block import BasicBlock
from ..utils.args import ARGS, BusInteractionHandlers
from ..utils.profiling import simple_profile
from .utils import *

FormulaWithAxioms = collections.namedtuple(
    "FormulaWithAxioms",
    ["constraints", "bus_interactions", "axioms", "derived", "globals"],
)


def _check_is_valid(self: Solver, f: FNode, assert_true=False) -> bool:
    try:
        logging.debug(f"checking whether {f} is valid")
        res = self.is_valid(f)
    except:
        logging.warning(f"failed to check whether {f} is valid")
        res = False
    if assert_true:
        assert res
    return res


def _check_is_sat(self: Solver, f: FNode, assert_true=False) -> bool:
    try:
        logging.debug(f"checking whether {f} is sat")
        res = self.is_sat(f)
    except:
        logging.warning(f"failed to check whether {f} is sat")
        res = False
    if assert_true:
        assert res
    return res


class SmtConverter:
    """Convert JSON-like APC dumps (constraints + bus interactions) into SMT constraints and axioms."""

    def __init__(self, name: str, basic_block: BasicBlock):
        """Create a converter that turns JSON-like dumps into SMT, namespacing symbols by `name`."""
        self.basic_block = basic_block
        self.field_symbols = set()
        self.constraints = []
        self.derived_columns = {}
        self.name = name
        self.constraint_solver = Solver(solver_options={":timeout": 5000})
        type(self.constraint_solver).check_is_valid = _check_is_valid
        type(self.constraint_solver).check_is_sat = _check_is_sat

        match ARGS().bus_interaction_handler:
            case BusInteractionHandlers.OPENVM:
                self.bus_interaction_encoder = (
                    bus_interactions.OpenVMBusInteractionEncoder(basic_block, self)
                )
            case _:
                logging.error(
                    f"Unsupported bus interaction handler: {ARGS().bus_interaction_handler}"
                )
                self.bus_interaction_encoder = None

    def __enter__(self):
        """No-op when entering a resource management context."""
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """Kill the solver when exiting a resource management context."""
        self.constraint_solver.exit()

    def __add_constraint(self, c: FNode, comment: Optional[str] = None):
        """Rewrite and store a constraint. Assert it to the utility solver"""
        if comment is not None:
            c = with_comment(c, comment)
        self.constraints.append(rewrite(c))
        self.constraint_solver.add_assertion(self.constraints[-1])

    def convert_constraints(self, data: Iterable[Any]):
        """Convert raw constraint expressions to `wrap_mod(expr) == 0` and add them."""
        for id, c in enumerate(data):
            self.__add_constraint(Equals(wrap_mod(c), Int(0)), f"CONSTRAINT #{id}")

    def convert_derived(self, data: Iterable[Any]):
        """Convert derived-column definitions into symbolic equalities (stored for later use)."""
        for derived in data:
            match derived:
                case [str(name), {"Constant": int(value)}]:
                    sym = Symbol(f"{self.name}-{name}", INT)
                    assert sym not in self.derived_columns
                    self.derived_columns[sym] = with_comment(
                        Int(value), f"DERIVED COLUMN {name} = {value}"
                    )
                case [str(name), {"QuotientOrZero": [a, b]}] | {
                    "variable": str(name),
                    "computation_method": {"QuotientOrZero": [a, b]},
                }:
                    sym = Symbol(f"{self.name}-{name}", INT)
                    assert sym not in self.derived_columns
                    a = self.convert_manual(a)
                    b = self.convert_manual(b)
                    self.derived_columns[sym] = with_comment(
                        rewrite(
                            Ite(Equals(b, Int(0)), Int(0), wrap_mod(Div(a, b)))
                        ),
                        f"DERIVED COLUMN {name} = QuotientOrZero({a}, {b})",
                    ),
                case _:
                    logging.error(f"Unsupported derived column: {derived}")

    @simple_profile
    def convert_manual(self, data: Any) -> Any:
        """Convert a JSON-like dump fragment (expression, machine, or interaction) into SMT terms."""
        match data:
            # general json structure
            case {
                "block": _,
                "machine": {
                    "constraints": list(cs),
                    "bus_interactions": list(bis),
                    "derived_columns": list(dcs),
                    **rest_machine,
                },
                "optimistic_constraints": _,
                "subs": _,
                **rest_apc,
            }:
                assert not rest_machine
                if "bus_map" in rest_apc:
                    self.bus_interaction_encoder.verify_bus_ids(rest_apc["bus_map"]["bus_ids"])
                    del rest_apc["bus_map"]
                assert not rest_apc
                
                logging.debug(f"{self.name}: converting constraints")
                self.convert_constraints(self.convert_manual(c) for c in cs)
                logging.debug(f"{self.name}: adding bus interaction")
                self.bus_interaction_encoder.add_all(
                    self.convert_manual(bi) for bi in bis
                )
                logging.debug(f"{self.name}: converting derived")
                self.convert_derived(dcs)

            # expressions
            case {"expr": expr, **rest}:
                assert rest == {}
                return self.convert_manual(expr)
            case [left, "+", right]:
                return Plus(self.convert_manual(left), self.convert_manual(right))
            case [left, "-", right]:
                return Minus(self.convert_manual(left), self.convert_manual(right))
            case [left, "*", right]:
                return Times(self.convert_manual(left), self.convert_manual(right))
            case ["-", right]:
                return Minus(Int(0), self.convert_manual(right))
            case int(value):
                return Int(value)
            case str(var):
                sym = Symbol(f"{self.name}-{var}", INT)
                self.field_symbols.add(sym)
                return sym

            # bus interactions
            case {"id": int(id), "mult": mult, "args": list(args)}:
                return {
                    "id": id,
                    "mult": self.convert_manual(mult),
                    "args": [self.convert_manual(arg) for arg in args],
                }

            case _:
                logging.error(f"Unsupported data in conversion: {data}")

    def __add_basic_range_axioms(self) -> Iterable[FNode]:
        """Generate and assert basic field-range axioms for all seen variable symbols."""
        for sym in sorted(self.field_symbols, key=lambda x: str(x)):
            fs = field_symbol(sym)
            self.constraint_solver.add_assertion(fs)
            yield fs

    @simple_profile
    def to_formula_with_axioms(self, data: Any) -> FormulaWithAxioms:
        """Convert input data and return constraints, interactions, axioms, derived columns, and globals."""
        logging.debug(f"{self.name}: converting")
        self.convert_manual(data)
        logging.debug(f"{self.name}: encoding bus interactions")
        bus_interactions = list(without_trues(self.bus_interaction_encoder.encode()))
        logging.debug(f"{self.name}: rewrite and assemble")
        fwa = FormulaWithAxioms(
            constraints=without_trues(self.constraints),
            bus_interactions=rewrite(bus_interactions),
            axioms=rewrite(
                list(without_trues(self.bus_interaction_encoder.get_axioms()))
                + list(self.__add_basic_range_axioms())
            ),
            derived=self.derived_columns,
            globals=self.bus_interaction_encoder.get_globals(),
        )
        if ARGS().log_smt:
            logging.info(f"after smt conversion:\n{pprint.pformat(fwa, width=80)}")
        logging.debug(f"{self.name}: done converting")
        return fwa
