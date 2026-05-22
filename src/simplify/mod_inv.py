"""Interpret the uninterpreted ``uf_mod_inv`` function.

``uf_mod_inv`` represents the modular multiplicative inverse in the
prime field.  The SMT encoding introduces it as an uninterpreted function
to allow for definitional equations that admit quantifier hoisting,
but to close the proof we must eventually give it meaning.

**Primary rewrite (definition-level folding).**  The ``uf_mod_inv`` function
is used within the QuotientOrZero derived column definitions with this pattern::

    (= V (mod (ite (= T 0) 0 (* C (uf_mod_inv T))) P))

i.e. ``V = C / T  (mod P)``  when ``T != 0``, and ``V = 0`` otherwise.
Naively replacing ``uf_mod_inv(T)`` with a fresh variable ``I`` and adding
``I * T ≡ 1 (mod P)`` introduces *two* nonlinear products (``I * T`` and
the pre-existing ``T * V`` elsewhere in the formula).

Instead we recognise the full definition and rewrite it to::

    T = 0  =>  V = 0
    T ≠ 0  =>  T * V ≡ C  (mod P)

This reuses V directly, leaving only one nonlinear product and letting Z3
solve the formula in < 1 s.

**Fallback rewrite.**  Any ``uf_mod_inv(T)`` that does *not* appear inside
the pattern above is still replaced with a fresh variable and the standard
inverse axiom ``T ≠ 0 => fresh * T ≡ 1 (mod P)``.
"""

from pysmt import substituter

from ..smt.conversion import SmtConverter
from ..smt.utils import *

UF_MOD_INV = SmtConverter.UF_MOD_INV


def _match_mod_inv_definition(formula: FNode):
    """Match the Skolem-derived ``uf_mod_inv`` definition pattern.

    Looks for::

        (= V (mod (ite (= T 0) 0 (* C (uf_mod_inv T))) P))

    where ``uf_mod_inv`` can appear in any position within the product.

    Returns ``(V, T, C, P)`` on success, else ``None``.
    """
    # Top level: (= V rhs)
    if not formula.is_equals():
        return None
    lhs, rhs = formula.arg(0), formula.arg(1)
    if not lhs.is_symbol():
        return None

    # rhs: (mod <ite> P)
    if rhs.node_type() != operators.MOD:
        return None
    p = rhs.arg(1)
    ite = rhs.arg(0)
    if not ite.is_ite():
        return None

    # ite: (ite (= T 0) 0 <product>)
    cond, then_br, else_br = ite.arg(0), ite.arg(1), ite.arg(2)
    if not (then_br.is_int_constant() and then_br.constant_value() == 0):
        return None
    if not cond.is_equals():
        return None
    ca, cb = cond.arg(0), cond.arg(1)
    if cb.is_int_constant() and cb.constant_value() == 0:
        t_var = ca
    elif ca.is_int_constant() and ca.constant_value() == 0:
        t_var = cb
    else:
        return None

    # product: (* ... (uf_mod_inv T) ...)
    if else_br.node_type() != operators.TIMES:
        return None
    factors = list(else_br.args())
    inv_idx = None
    for i, f in enumerate(factors):
        if f.is_function_application() and f.function_name() == UF_MOD_INV:
            inv_idx = i
            break
    if inv_idx is None:
        return None

    # Verify that uf_mod_inv is applied to the same term as the ITE condition.
    inv_node = factors[inv_idx]
    inv_of = inv_node.arg(0)
    if not _structurally_equal(inv_of, t_var):
        return None

    # Remaining factors form the coefficient C in V = C / T.
    others = [f for i, f in enumerate(factors) if i != inv_idx]
    c = others[0] if len(others) == 1 else Times(*others)
    return (lhs, t_var, c, p)


def _structurally_equal(a: FNode, b: FNode) -> bool:
    """Cheap structural equality via serialized SMT-LIB text."""
    return a.serialize() == b.serialize()


class _FallbackModInvRewriter(substituter.Substituter):
    """Fallback for ``uf_mod_inv`` occurrences outside the definition pattern.

    Each ``uf_mod_inv(t)`` is replaced by a fresh integer variable and
    constrained with ``t != 0 => fresh * t ≡ 1 (mod p)``.  This is the
    naive encoding that introduces a nonlinear product; it is only used
    when the definition-level folding above does not apply.
    """

    def __init__(self, env=None):
        """Prepare fresh-symbol allocator and side-effect constraint list."""
        super().__init__(env=env)
        self._fresh_counter = 0
        self._replacement_by_term = {}
        self.new_symbols = []
        self.constraints = []

    def _fresh_symbol(self) -> FNode:
        """Allocate ``__mod_inv_N`` for a fallback replacement."""
        sym = Symbol(f"__mod_inv_{self._fresh_counter}", INT)
        self._fresh_counter += 1
        return sym

    def rewrite(self, formula: FNode) -> FNode:
        """Iteratively replace ``uf_mod_inv`` leaves with fresh vars and inverse axioms."""
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
                            Implies(
                                Not(Equals(wrap_mod(t), Int(0))),
                                Equals(wrap_mod(Times(replacement, t)), Int(1))
                            )
                        )
                    memo[node] = keep_comment(replacement, node)
                else:
                    memo[node] = keep_comment(
                        substituter.Substituter.super(self, node, args=args, interpretations={}), node
                    )
                continue
            stack.append((node, True))
            if node.is_forall() or node.is_exists():
                continue
            for arg in node.args():
                stack.append((arg, False))
        return memo[formula]


def simplify_mod_inv(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Rewrite all ``uf_mod_inv`` applications into interpreted constraints.

    Two strategies are tried per assertion, in order:

    1. **Definition-level folding** — if the whole assertion matches the
       Skolem-derived pattern ``V = (ite (= T 0) 0 (* C (uf_mod_inv T))) mod P``,
       replace it with two implications that constrain ``V`` directly,
       avoiding an intermediate variable and the extra nonlinear product
       it would entail.

    2. **Per-term fallback** — any leftover ``uf_mod_inv(T)`` is replaced
       by a fresh ``__mod_inv_N`` variable with an explicit inverse axiom.
    """
    declared = {
        cmd.args[0].symbol_name()
        for cmd in smt_script
        if cmd.name == "declare-fun"
    }
    rewriter = _FallbackModInvRewriter()
    output = []
    for cmd in smt_script:
        if cmd.name != "assert":
            output.append(cmd)
            continue

        # --- Strategy 1: definition-level fold ---
        m = _match_mod_inv_definition(cmd.args[0])
        if m is not None:
            var, t, c, p = m
            # T = 0 => V = 0  (zero-divisor case)
            output.append(script.SmtLibCommand(
                name="assert",
                args=[Implies(Equals(wrap_mod(t), Int(0)), Equals(var, Int(0)))],
            ))
            # T ≠ 0 => T * V ≡ C  (mod P)  —  the key: only one nonlinear product
            output.append(script.SmtLibCommand(
                name="assert",
                args=[Implies(
                    Not(Equals(wrap_mod(t), Int(0))),
                    Equals(Mod(Times(t, var), p), Mod(c, p)),
                )],
            ))
            continue

        # --- Strategy 2: per-term fallback ---
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
