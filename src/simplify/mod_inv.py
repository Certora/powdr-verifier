from pysmt import substituter

from ..smt.conversion import SmtConverter
from ..smt.utils import *

UF_MOD_INV = SmtConverter.UF_MOD_INV


class _OutsideQuantifierModInvRewriter(substituter.Substituter):
    def __init__(self, env=None):
        super().__init__(env=env)
        self._fresh_counter = 0
        self._replacement_by_term = {}
        self.new_symbols = []
        self.constraints = []

    def _fresh_symbol(self) -> FNode:
        sym = Symbol(f"__mod_inv_{self._fresh_counter}", INT)
        self._fresh_counter += 1
        return sym

    def rewrite(self, formula: FNode) -> FNode:
        memo: dict[FNode, FNode] = {}
        stack = [(formula, False)]
        while stack:
            node, expanded = stack.pop()
            if node in memo:
                continue
            if expanded:
                if node.is_forall() or node.is_exists():
                    memo[node] = node
                    continue
                args = [memo[arg] for arg in node.args()]
                if node.is_function_application() and node.function_name() == UF_MOD_INV:
                    replacement = self._replacement_by_term.get(node)
                    if replacement is None:
                        replacement = self._fresh_symbol()
                        self._replacement_by_term[node] = replacement
                        self.new_symbols.append(replacement)
                        t = args[0]
                        self.constraints.append(
                            Equals(wrap_mod(Times(replacement, t)), Int(1))
                        )
                    memo[node] = keep_comment(replacement, node)
                else:
                    memo[node] = keep_comment(
                        substituter.Substituter.super(self, node, args=args), node
                    )
                continue
            stack.append((node, True))
            if node.is_forall() or node.is_exists():
                continue
            for arg in node.args():
                stack.append((arg, False))
        return memo[formula]


def simplify_mod_inv(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    declared = {
        cmd.args[0].symbol_name()
        for cmd in smt_script
        if cmd.name == "declare-fun"
    }
    output = []
    for cmd in smt_script:
        if cmd.name != "assert":
            output.append(cmd)
            continue
        rewriter = _OutsideQuantifierModInvRewriter()
        cmd.args[0] = rewriter.rewrite(cmd.args[0])
        for sym in rewriter.new_symbols:
            if sym.symbol_name() in declared:
                continue
            output.append(script.SmtLibCommand(name="declare-fun", args=[sym]))
            declared.add(sym.symbol_name())
        output.append(cmd)
        output.extend(
            script.SmtLibCommand(name="assert", args=[constraint])
            for constraint in rewriter.constraints
        )
    smt_script.commands = output
    return smt_script
