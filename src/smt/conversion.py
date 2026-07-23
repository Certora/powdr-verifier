"""JSON APC dump to PySMT: ``SmtConverter`` and ``FormulaWithAxioms`` bundle."""
import collections
import itertools
import logging
import pprint
from pathlib import Path
from typing import Any, Iterable, Optional


from .. import bus_interactions
from ..utils.basic_block import BasicBlock
from ..utils.args import ARGS, BusInteractionHandlers
from ..verify.membus_analysis import MembusAnalysis
from .utils import *

FormulaWithAxioms = collections.namedtuple(
    "FormulaWithAxioms",
    ["constraints", "consequences", "axioms", "derived", "globals"],
)
FormulaWithAxioms.__doc__ = """Structured PySMT bundle produced by ``SmtConverter``.

``constraints`` are the statements the circuit commits to (algebraic
constraints and bus-interaction semantics). ``consequences`` are statements
*derived from* the constraints (e.g. inferred variable ranges, "exchanged
memory values are field elements") — true whenever the constraints hold, but
NOT themselves circuit commitments. ``encoding()`` adds the constraints of both
programs but the consequences of the reference (before) program only, so a
derived fact never becomes a proof obligation on the checked (after) side.

``axioms`` are granted environment assumptions (asserted for both sides).
``derived`` maps column symbols to lists of defining formulas (a symbol may
have more than one); ``globals`` collects symbols treated as rigid across
quantifier prefixes.
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

    def __init__(
        self,
        name: Optional[str],
        basic_block: BasicBlock,
        *,
        memory_bus_alignment: MembusAnalysis | None = None,
        source_path: Path | None = None,
    ):
        """Create a converter that turns JSON-like dumps into SMT, namespacing symbols by `name`."""
        self.basic_block = basic_block
        self.constraints = []
        self.derived_columns: dict[FNode, list[FNode]] = collections.defaultdict(list)
        self.name = name
        self.memory_bus_alignment = memory_bus_alignment
        self.source_path = source_path
        self.symbols: set[FNode] = set()
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
    
    def _symbol(self, name: str, sort, add_prefix=True) -> FNode:
        if add_prefix and self.name is not None:
            sym = Symbol(f"{self.name}-{name}", sort)
        else:
            sym = Symbol(name, sort)
        self.symbols.add(sym)
        return sym

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

    def convert_computation_method(self, cm: Any) -> FNode:
        match cm:
            case {"Constant": int(value)}:
                return Int(value)
            case {"QuotientOrZero": [a, b]}:
                ae, be = self.convert_manual(a), self.convert_manual(b)
                return Ite(
                    field_eq(be),
                    Int(0),
                    Times(wrap_mod(ae), Function(self.UF_MOD_INV, [wrap_mod(be)])),
                )
            case {"IfEqZero": [cond, then_cm, else_cm]}:
                ce = self.convert_manual(cond)
                return Ite(
                    field_eq(ce),
                    self.convert_computation_method(then_cm),
                    self.convert_computation_method(else_cm),
                )
            case _:
                logging.error(f"Unsupported computation method: {cm}")
                return Int(0)

    def convert_derived(self, data: Iterable[Any]):
        """Convert derived-column definitions into symbolic equalities (stored for later use).

        A single symbol may carry multiple defining equalities (powdr's
        ``remove_free`` can emit several derived rows for the same column),
        so definitions are appended to a per-symbol list.
        """
        for derived in data:
            match derived:
                case [bool(_), str(name), cm] | [str(name), cm]:
                    sym = self._symbol(name, INT)
                    self.derived_columns[sym].append(
                        with_comment(
                            Equals(sym, self.convert_computation_method(cm)),
                            f"DERIVED COLUMN {name}",
                        )
                    )
                case _:
                    logging.error(f"Unsupported derived column: {derived}")
                    continue

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
    
    def convert_substitutions(self, data: Iterable[Any]):
        """Convert APC substitution pairs into SMT ``Equals`` terms."""
        return {
            self.convert_manual(k): Equals(self.convert_manual(k), self.convert_manual(v))
            for k, v in data
        }

    def to_formula_with_axioms(self, data: Any) -> FormulaWithAxioms:
        """Convert input data and return constraints, interactions, axioms, derived columns, and globals."""
        logging.debug(f"{self.name}: converting")
        self.convert_manual(data)
        logging.debug(f"{self.name}: assemble")
        # `encode()` yields the circuit's committed constraints; it must be
        # consumed before `consequences()` (which reads the derived facts each
        # encoder stashes while encoding).
        constraints = list(itertools.chain(
            without_trues(self.constraints),
            without_trues(self.bus_interaction_encoder.encode())
        ))
        consequences = list(without_trues(self.bus_interaction_encoder.get_consequences()))
        if not ARGS().skip_range_inference:
            # Ranges inferred from the constraints are derived facts, not
            # circuit commitments -> consequences, not constraints.
            consequences += self.bus_interaction_encoder.memory.infer_unconditional_ranges(
                constraints
            )
        axioms = list(without_trues(self.bus_interaction_encoder.get_axioms()))
        derived = {k: list(v) for k, v in self.derived_columns.items()}
        fwa = FormulaWithAxioms(
            constraints=constraints,
            consequences=consequences,
            axioms=axioms,
            derived=derived,
            globals=self.bus_interaction_encoder.get_globals() | frozenset([self.UF_MOD_INV]),
        )
        logging.debug(f"{self.name}: done converting")
        return fwa
