"""JSON APC dump to PySMT: ``SmtConverter`` and ``FormulaWithAxioms`` bundle."""
import collections
import itertools
import logging
import pprint
from typing import Any, Iterable


from .. import bus_interactions
from ..utils.basic_block import BasicBlock
from ..utils.args import ARGS, BusInteractionHandlers
from ..utils.profiling import simple_profile
from .utils import *

FormulaWithAxioms = collections.namedtuple(
    "FormulaWithAxioms",
    ["constraints", "axioms", "derived", "globals"],
)
FormulaWithAxioms.__doc__ = """Structured PySMT bundle produced by ``SmtConverter``.

``constraints`` and ``axioms`` are lists of ``FNode``; ``derived`` maps column
symbols to defining formulas; ``globals`` collects symbols treated as rigid
across quantifier prefixes.
"""


def _check_is_valid(self: Solver, f: FNode) -> bool:
    try:
        logging.debug(f"checking whether {f} is valid")
        return self.is_valid(f)
    except:
        logging.warning(f"failed to check whether {f} is valid")
        return False


class SmtConverter:
    """Convert JSON-like APC dumps (constraints + bus interactions) into SMT constraints and axioms."""
    UF_MOD_INV = Symbol("uf_mod_inv", FunctionType(INT, [INT]))

    def __init__(self, name: Optional[str], basic_block: BasicBlock):
        """Create a converter that turns JSON-like dumps into SMT, namespacing symbols by `name`."""
        self.basic_block = basic_block
        self.constraints = []
        self.derived_columns = {}
        self.name = name
        self.constraint_solver = Solver(solver_options={":timeout": 2000})
        type(self.constraint_solver).check_is_valid = _check_is_valid

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
    
    def _symbol(self, name: str, sort) -> FNode:
        if self.name is not None:
            return Symbol(f"{self.name}-{name}", sort)
        return Symbol(name, sort)

    def __enter__(self):
        """No-op when entering a resource management context."""
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """Kill the solver when exiting a resource management context."""
        self.constraint_solver.exit()

    def __add_constraint(self, c: FNode, comment: Optional[str] = None):
        """Store a constraint. Assert it to the utility solver"""
        if comment is not None:
            c = with_comment(c, comment)
        self.constraints.append(c)
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
                    sym = self._symbol(name, INT)
                    assert sym not in self.derived_columns
                    self.derived_columns[sym] = with_comment(
                        Equals(sym, Int(value)), f"DERIVED COLUMN {name} = {value}"
                    )
                case [str(name), {"QuotientOrZero": [a, b]}] | {
                    "variable": str(name),
                    "computation_method": {"QuotientOrZero": [a, b]},
                }:
                    sym = self._symbol(name, INT)
                    assert sym not in self.derived_columns
                    a = self.convert_manual(a)
                    b = self.convert_manual(b)
                    self.derived_columns[sym] = with_comment(
                        Equals(
                            sym,
                            Ite(
                                Equals(wrap_mod(b), Int(0)),
                                Int(0),
                                Times(
                                    wrap_mod(a),
                                    Function(self.UF_MOD_INV, [wrap_mod(b)]),
                                )
                            ),
                        ),
                        f"DERIVED COLUMN {name} = QuotientOrZero({a}, {b})",
                    )
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
                    self.bus_interaction_encoder.configure_from_bus_ids(rest_apc["bus_map"]["bus_ids"])
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
                return self._symbol(var, INT)

            # bus interactions
            case {"id": int(id), "mult": mult, "args": list(args)}:
                return {
                    "id": id,
                    "mult": self.convert_manual(mult),
                    "args": [self.convert_manual(arg) for arg in args],
                }

            case _:
                logging.error(f"Unsupported data in conversion: {data}")
    
    def convert_eliminations(self, data: Iterable[Any]):
        """Convert eliminations into SMT terms."""
        return {
            self.convert_manual(k): Equals(self.convert_manual(k), self.convert_manual(v))
            for k, v in data
        }

    @simple_profile
    def to_formula_with_axioms(self, data: Any) -> FormulaWithAxioms:
        """Convert input data and return constraints, interactions, axioms, derived columns, and globals."""
        logging.debug(f"{self.name}: converting")
        self.convert_manual(data)
        logging.debug(f"{self.name}: assemble")
        constraints = list(itertools.chain(
            without_trues(self.constraints),
            without_trues(self.bus_interaction_encoder.encode())
        ))
        axioms = list(without_trues(self.bus_interaction_encoder.get_axioms()))
        live = set()
        for f in itertools.chain(constraints, axioms):
            live.update(f.get_free_variables())
        remaining_derived = dict(self.derived_columns)
        derived = {}
        while True:
            used = {
                sym: constraint
                for sym, constraint in remaining_derived.items()
                if sym in live
            }
            if not used:
                break
            for sym, constraint in used.items():
                derived[sym] = constraint
                live.update(constraint.get_free_variables())
                del remaining_derived[sym]
        fwa = FormulaWithAxioms(
            constraints=constraints,
            axioms=axioms,
            derived=derived,
            globals=self.bus_interaction_encoder.get_globals() | frozenset([self.UF_MOD_INV]),
        )
        logging.debug(f"{self.name}: done converting")
        return fwa
