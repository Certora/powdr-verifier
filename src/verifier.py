import json
import sympy


from .rewriter.conversion import to_smt, to_sympy
from .rewriter import rewrite
from .smt.encoding import build_input_output_relation, collect_variables
from .smt.conversion import FormulaWithAxioms, SmtConverter, check_formula
from .smt.utils import *
from .utils.basic_block import BasicBlock

BEFORE_PREFIX = "before"
AFTER_PREFIX = "after"


def strip_prefix(name: str) -> str:
    """Remove the verifier-added `before-`/`after-` prefix from a symbol name."""
    if name.startswith(BEFORE_PREFIX):
        return name[len(BEFORE_PREFIX) + 1 :]
    elif name.startswith(AFTER_PREFIX):
        return name[len(AFTER_PREFIX) + 1 :]
    return name


class ModelMapBuilder:
    def __init__(
        self,
        old: frozenset[FNode],
        new: frozenset[FNode],
        oldf: FormulaWithAxioms,
        newf: FormulaWithAxioms,
    ):
        """Initialize a heuristic builder for mapping variables between two encodings."""
        self.old = old
        self.new = new
        self.oldf = oldf
        self.newf = newf

        self.omap = {strip_prefix(v.symbol_name()): v for v in old}
        self.nmap = {strip_prefix(v.symbol_name()): v for v in new}
        self.nderivedmap = {strip_prefix(v[0].symbol_name()): v for v in newf.derived}
        self.result = {}

    def __check(self):
        """Warn if not all `new` variables were mapped; return True iff the map is complete."""
        if self.nmap:
            logging.warning(
                "model map is not complete, this can produce false positives"
            )
            logging.debug(f"have: {self.result.keys()}")
            logging.warning(f"missing: {', '.join(self.nmap.keys())}")
            return False
        return True

    def __heuristic_same_name(self):
        """Add variables with the same name to the result"""
        for k in self.omap.keys() & self.nmap.keys():
            self.result[self.nmap[k]] = self.omap[k]
            del self.nmap[k]
            del self.omap[k]

    def __heuristic_derived(self):
        """Add derived variables to the result"""
        for v in self.nderivedmap.values():
            logging.debug(f"derived: found {v[0]} = {v[1]}")
            self.result[v[0]] = v[1]
        self.nderivedmap = {}

    def __heuristic_simple_equality(self):
        """Add variables that have a unique solution from some constraint to the result"""
        for c in self.newf.constraints:
            if not c.is_equals():
                continue
            c = c.substitute({v: c for v, c in self.result.items() if c.is_constant()})
            c = rewrite(c)
            vars = c.get_free_variables()
            if len(vars) == 1:
                solution = sympy.solve(to_sympy(c), dict=True)
                if len(solution) == 1:
                    for r, v in solution[0].items():
                        target = strip_prefix(r.name)
                        logging.debug(f"simpeq: found {target} = {v}")
                        if target not in self.nmap:
                            continue
                        assert target not in self.omap
                        v = to_smt(v)
                        self.result[self.nmap[target]] = v
                        del self.nmap[target]

    def __heuristic_pclookup(self, conv):
        """Derive variable values from a resolved PC lookup interaction when possible."""
        encoder = conv.bus_interaction_encoder.pc_lookup
        for i in encoder._interactions:
            mult, (spc, sop, sa, sb, sc, sd, se, sf, sg) = i
            if spc in self.result and self.result[spc].is_constant():
                op, a, b, c, d, e, f, g = encoder._get_instruction(
                    self.result[spc].constant_value()
                )

                res = find_unique_solution(conv.constraint_solver, Equals(sop, Int(op)))
                if res is not None:
                    for v, c in res.items():
                        logging.debug(f"pclookup: found {v} = {c}")
                        self.result[v] = c
                        del self.nmap[strip_prefix(v.symbol_name())]

    def build(self, newconv):
        """Run all heuristics in sequence to populate the variable mapping."""
        self.__heuristic_same_name()
        self.__heuristic_derived()
        self.__heuristic_simple_equality()
        self.__heuristic_pclookup(newconv)
        self.__heuristic_simple_equality()
        self.__check()

    @attach_comment("MODEL MAP")
    def get_map(self):
        """Return the computed mapping as a conjunction of equalities."""
        return And(*[Equals(a, b) for a, b in self.result.items()])


def do_check(f: FNode, name: str):
    """Check satisfiability of `f` and print a human-friendly result (and counterexample if any)."""
    match check_formula(f, name):
        case False, _:
            print(f"{name} is proven")
        case None, _:
            print(f"could not solve {name}, solver returned UNKNOWN")
        case True, model:
            print(f"{name} is violated")
            model = to_nice_model(model)
            print(json.dumps(model, indent=4))


def verify(before: FNode, after: FNode, block: BasicBlock):
    """Verify our versions of equivalence."""

    with (
        SmtConverter(BEFORE_PREFIX, block) as before_conv,
        SmtConverter(AFTER_PREFIX, block) as after_conv,
    ):
        before_smt = before_conv.to_formula_with_axioms(before)
        after_smt = after_conv.to_formula_with_axioms(after)

        # obtain input and output info
        inputs1 = before_conv.bus_interaction_encoder.get_inputs()
        inputs2 = after_conv.bus_interaction_encoder.get_inputs()
        outputs1 = before_conv.bus_interaction_encoder.get_outputs()
        outputs2 = after_conv.bus_interaction_encoder.get_outputs()
        input_relation = build_input_output_relation("INPUT RELATION", inputs1, inputs2)
        output_relation = build_input_output_relation(
            "OUTPUT RELATION", outputs1, outputs2
        )

        # obtain variables and globals
        var1 = collect_variables(before_smt)
        var2 = collect_variables(after_smt)
        globals = before_smt.globals | after_smt.globals
        auxiliaries = (
            before_conv.bus_interaction_encoder.get_auxiliaries()
            | after_conv.bus_interaction_encoder.get_auxiliaries()
        )

        def completeness():
            forward_builder = ModelMapBuilder(
                var1 - globals - auxiliaries,
                var2 - globals - auxiliaries,
                before_smt,
                after_smt,
            )
            forward_builder.build(after_conv)
            completeness = ForAll(
                var2 - globals,
                And(
                    And(
                        *before_smt.constraints,
                        *before_smt.bus_interactions,
                        forward_builder.get_map(),
                        input_relation,
                        output_relation,
                    ),
                    Not(
                        And(
                            *after_smt.constraints,
                            *after_smt.bus_interactions,
                        )
                    ),
                    And(*before_smt.axioms),
                    And(*after_smt.axioms),
                ),
            )
            do_check(completeness, "completeness")

        completeness()

        def soundness():
            backward_builder = ModelMapBuilder(
                var2 - globals - auxiliaries,
                var1 - globals - auxiliaries,
                after_smt,
                before_smt,
            )
            backward_builder.build(before_conv)
            soundness = ForAll(
                var1 - globals,
                And(
                    Not(
                        Implies(
                            And(
                                *after_smt.constraints,
                                *after_smt.bus_interactions,
                                backward_builder.get_map(),
                                input_relation,
                                output_relation,
                            ),
                            And(
                                *before_smt.constraints,
                                *before_smt.bus_interactions,
                            ),
                        )
                    ),
                    And(*before_smt.axioms),
                    And(*after_smt.axioms),
                ),
            )
            do_check(soundness, "soundness")

        soundness()

        def determinism():
            # determinism: if an input has a trace for both programs, the outputs are the same
            determinism = And(
                Not(
                    Implies(
                        And(
                            *before_smt.constraints,
                            *before_smt.bus_interactions,
                            *after_smt.constraints,
                            *after_smt.bus_interactions,
                            input_relation,
                        ),
                        And(common_intermediates, output_relation),
                    )
                ),
                And(*before_smt.axioms),
                And(*after_smt.axioms),
            )
            do_check(determinism, "determinism")

        # determinism()
