import json
import sympy


from .encoding.utils import get_is_valid
from .report.action import Action
from .rewriter.conversion import to_smt, to_sympy
from .rewriter import rewrite
from .smt.encoding import build_input_output_relation, collect_variables
from .smt.conversion import FormulaWithAxioms, SmtConverter
from .smt.utils import *
from .utils.basic_block import BasicBlock
from .utils.io import load_apc_dump, load_json

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
        derived: dict[str, FNode],
    ):
        """Initialize a heuristic builder for mapping variables between two encodings."""
        self.old = old
        self.new = new
        self.oldf = oldf
        self.newf = newf
        self.derived = derived

        # maps stripped names to old symbols
        self.omap = {strip_prefix(v.symbol_name()): v for v in old}
        # maps stripped names to new symbols
        self.nmap = {strip_prefix(v.symbol_name()): v for v in new}
        # maps stripped names to new expressions
        self.nderivedmap = {strip_prefix(k.symbol_name()): v for k,v in derived.items()}
        # maps new variables to expressions
        self.result = {}
        self.todo = set(self.nmap.keys())
    
    def __add_result(self, name: str, value: FNode):
        """Add a result to the result map"""
        k = self.nmap[name]
        if name not in self.todo:
            assert self.result[k] == value
            return
        self.result[k] = value
        self.todo.remove(name)

    def __check(self):
        """Warn if not all `new` variables were mapped; return True iff the map is complete."""
        if self.todo:
            logging.info("model map is not complete, this can cause slowdowns")
            logging.debug("have:")
            for k,v in self.result.items():
                logging.debug(f"\t{k} = {v}")
            logging.debug("missing:")
            for k in self.todo:
                logging.debug(f"\t{k}")
            return False
        return True

    def __heuristic_same_name(self):
        """Add variables with the same name to the result"""
        for k in self.todo & self.omap.keys():
            self.result[self.nmap[k]] = self.omap[k]
            self.todo.remove(k)

    def __heuristic_derived(self):
        """Add derived variables to the result"""
        for k in self.todo & self.nderivedmap.keys():
            v = self.nderivedmap[k]
            logging.debug(f"derived: found {k} = {v}")
            self.__add_result(k, v)
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
                        self.__add_result(target, to_smt(v))

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
                        self.__add_result(strip_prefix(v.symbol_name()), c)

    def build(self, newconv):
        """Run all heuristics in sequence to populate the variable mapping."""
        self.__heuristic_same_name()
        self.__heuristic_derived()
        #self.__heuristic_simple_equality()
        self.__heuristic_pclookup(newconv)
        #self.__heuristic_simple_equality()
        self.__check()

    @attach_comment("MODEL MAP")
    def get_map(self):
        """Return the computed mapping as a conjunction of equalities."""
        s = sorted(self.result.items(), key=lambda x: x[0].symbol_name())
        return And(*[Equals(a, wrap_mod(b)) for a, b in s])
    
    def get_skolemized_variables(self) -> frozenset:
        """Return the computed mapping as a conjunction of equalities."""
        return frozenset(self.result.keys())


def encoding(before, after, qvars, builder, input_relation, output_relation, additional_asserts=[]):
    if ARGS().elim_with_skolem:
        res = And(
            *before.constraints,
            ForAll(
                qvars - builder.result.keys(),
                Or(
                    Not(And(*after.constraints)),
                    Not(input_relation),
                    Not(output_relation)
                ).substitute(builder.result)
            ),
            *before.axioms,
            *after.axioms,
            *additional_asserts,
        )
    else:
        res = And(
            *before.constraints,
            ForAll(
                qvars,
                Implies(
                    builder.get_map(),
                    Or(
                        Not(And(*after.constraints)),
                        Not(input_relation),
                        Not(output_relation)
                    )
                )
            ),
            *after.axioms,
            *before.axioms,
            *additional_asserts,
        )
    if ARGS().elim_with_model:
        model = load_json(ARGS().elim_with_model)
        subs = {}
        for name, value in model.items():
            if isinstance(value, bool):
                subs[Symbol(name, BOOL)] = Bool(value)
            elif isinstance(value, int):
                subs[Symbol(name, INT)] = Int(value)
        res = res.substitute(subs)
    return res

def verify():
    """Verify our versions of equivalence."""

    before = load_apc_dump(ARGS().input_before)
    after = load_apc_dump(ARGS().input_after)

    block = BasicBlock(before["block"])
    assert block == BasicBlock(after["block"]), "The basic block has changed"

    with (
        Action("verify-encode") as action,
        SmtConverter(BEFORE_PREFIX, block) as before_conv,
        SmtConverter(AFTER_PREFIX, block) as after_conv,
    ):
        action += {"outputs": []}
        before_smt = before_conv.to_formula_with_axioms(before)
        after_smt = after_conv.to_formula_with_axioms(after)

        eliminations = {}
        if ARGS().eliminations is not None:
            eliminations = before_conv.convert_eliminations(load_json(ARGS().eliminations))


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
        auxiliaries = frozenset.union(frozenset(), *(
            before_conv.bus_interaction_encoder.get_auxiliaries()
            | after_conv.bus_interaction_encoder.get_auxiliaries()
        ).values())

        outfile = ARGS().output.with_suffix(".completeness.smt2")
        with open(outfile, "w") as dump:
            dump.write(";; completeness check\n")
            forward_builder = ModelMapBuilder(
                var1 - globals - auxiliaries,
                var2 - globals - auxiliaries,
                before_smt,
                after_smt,
                after_smt.derived,
            )
            forward_builder.build(after_conv)
            completeness = encoding(before_smt, after_smt, var2 - globals, forward_builder, input_relation, output_relation)

            logging.info(f"dumping completeness check to {dump.name}")
            smtlib = convert_to_smt_script(completeness, status='unsat')
            pretty_print_smtlib(smtlib, dump)
            action += ("outputs", outfile)
        
        is_valid_before = get_is_valid(var1, "before")
        is_valid_after = get_is_valid(var2, "after")

        if is_valid_before is None and is_valid_after is not None:
            logging.warning("is_valid was introduced, perform special soundness check")
            outfile = ARGS().output.with_suffix(".soundness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; soundness check\n")
                backward_builder = ModelMapBuilder(
                    var2 - globals - auxiliaries,
                    var1 - globals - auxiliaries,
                    after_smt,
                    before_smt,
                    eliminations,
                )
                backward_builder.build(before_conv)
                soundness = encoding(after_smt, before_smt, var1 - globals, backward_builder, input_relation, output_relation, additional_asserts=[Equals(is_valid_after, Int(1))])

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(soundness, status='unsat')
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)

            outfile = ARGS().output.with_suffix(".soundness.zero-is-model.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; check that all zero is a model\n")
                logging.info(f"dumping zero is model check to {dump.name}")
                intvars = [ v for v in (var2 - auxiliaries) if v.get_type() == INT ]
                intvars = sorted(intvars, key=lambda x: x.symbol_name())
                smtlib = convert_to_smt_script(
                    And(
                        *after_smt.constraints,
                        *after_smt.axioms,
                        with_comment(
                            And(*[ Equals(v, Int(0)) for v in intvars ]),
                            "ZERO MODEL"
                        )
                    ),
                    status='sat'
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)

            outfile = ARGS().output.with_suffix(".soundness.invalid-all-mult-zero.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; check that all is_valid zero makes all multiplicities zero\n")
                logging.info(f"dumping invalid makes all multiplicities zero check to {dump.name}")

                multiplicities = []
                for encoder in after_conv.bus_interaction_encoder.encoders:
                    for interaction in encoder._interactions:
                        multiplicities.append(interaction.mult)
                smtlib = convert_to_smt_script(
                    And(
                        Equals(is_valid_after, Int(0)),
                        *after_smt.constraints,
                        Or(*[Not(Equals(mult, Int(0))) for mult in multiplicities ])
                    ),
                    status='unsat'
                )
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)
        else:
            outfile = ARGS().output.with_suffix(".soundness.smt2")
            with open(outfile, "w") as dump:
                dump.write(";; soundness check\n")
                backward_builder = ModelMapBuilder(
                    var2 - globals - auxiliaries,
                    var1 - globals - auxiliaries,
                    after_smt,
                    before_smt,
                    eliminations,
                )
                backward_builder.build(before_conv)
                soundness = encoding(after_smt, before_smt, var1 - globals, backward_builder, input_relation, output_relation)

                logging.info(f"dumping soundness check to {dump.name}")
                smtlib = convert_to_smt_script(soundness, status='unsat')
                pretty_print_smtlib(smtlib, dump)
                action += ("outputs", outfile)
        action += {"result": "success"}

    return action