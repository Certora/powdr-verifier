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

    Accepts both shapes the encoder may emit::

        (= V (mod (ite (= T       0) 0 (* C (uf_mod_inv T))) P))         ; outer-mod
        (= V (ite      (= (mod T P) 0) 0 (* C (uf_mod_inv (mod T P)))))  ; inner-mod
        ; (and any consistent combination — mods may appear on T inside the
        ; condition, inside ``uf_mod_inv``, or wrap the whole ite)

    All ``(mod _ P)`` wrappers must use the same modulus ``P``. ``C`` is
    returned as-is (any further ``(mod _ P)`` on coefficients is left for the
    emission step, which already wraps the final RHS in ``(mod c p)``).

    Returns ``(V, T, C, P)`` on success, else ``None``.
    """
    # Top level: (= V rhs)
    if not formula.is_equals():
        return None
    lhs, rhs = formula.arg(0), formula.arg(1)
    if not lhs.is_symbol():
        return None

    # Optional outer (mod _ P) wrapper around the ite.
    p = None
    if rhs.node_type() == operators.MOD:
        p = rhs.arg(1)
        ite = rhs.arg(0)
    else:
        ite = rhs
    if not ite.is_ite():
        return None

    # ite: (ite (= T 0) 0 <product>)
    cond, then_br, else_br = ite.arg(0), ite.arg(1), ite.arg(2)
    if then_br.node_type() != operators.INT_CONSTANT or int(then_br.constant_value()) != 0:
        return None
    if not cond.is_equals():
        return None
    ca, cb = cond.arg(0), cond.arg(1)
    if cb.node_type() == operators.INT_CONSTANT and int(cb.constant_value()) == 0:
        t_raw = ca
    elif ca.node_type() == operators.INT_CONSTANT and int(ca.constant_value()) == 0:
        t_raw = cb
    else:
        return None

    # T may itself be (mod T_inner P); strip and reconcile P.
    if t_raw.node_type() == operators.MOD:
        if p is None:
            p = t_raw.arg(1)
        elif not _structurally_equal(p, t_raw.arg(1)):
            return None
        t_var = t_raw.arg(0)
    else:
        t_var = t_raw

    # else_br is either a product (* ... (uf_mod_inv <arg>) ...) or a bare
    # (uf_mod_inv <arg>) when C=1 and the surrounding Times got folded away.
    if else_br.is_function_application() and else_br.function_name() == UF_MOD_INV:
        factors = [else_br]
        inv_idx = 0
    elif else_br.node_type() == operators.TIMES:
        factors = list(else_br.args())
        inv_idx = None
        for i, f in enumerate(factors):
            if f.is_function_application() and f.function_name() == UF_MOD_INV:
                inv_idx = i
                break
        if inv_idx is None:
            return None
    else:
        return None

    # uf_mod_inv's argument may be wrapped (mod T_inner P); strip and reconcile.
    inv_node = factors[inv_idx]
    inv_of_raw = inv_node.arg(0)
    if inv_of_raw.node_type() == operators.MOD:
        if p is None:
            p = inv_of_raw.arg(1)
        elif not _structurally_equal(p, inv_of_raw.arg(1)):
            return None
        inv_of = inv_of_raw.arg(0)
    else:
        inv_of = inv_of_raw

    if not _structurally_equal(inv_of, t_var):
        return None

    # We must have found the modulus somewhere along the way.
    if p is None:
        return None

    # Remaining factors form the coefficient C in V = C / T.
    others = [f for i, f in enumerate(factors) if i != inv_idx]
    if not others:
        c = Int(1)
    elif len(others) == 1:
        c = others[0]
    else:
        c = Times(*others)
    return (lhs, t_var, c, p)


def _structurally_equal(a: FNode, b: FNode) -> bool:
    """Cheap structural equality via serialized SMT-LIB text."""
    return a.serialize() == b.serialize()


def _contains_mod_inv(formula: FNode) -> bool:
    """True if ``formula`` contains a ``uf_mod_inv`` application."""
    stack = [formula]
    while stack:
        node = stack.pop()
        if node.is_function_application() and node.function_name() == UF_MOD_INV:
            return True
        stack.extend(node.args())
    return False


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


def simplify_mod_inv(smt_script: script.SmtLibScript, subaction=None) -> script.SmtLibScript:
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
    if not any(
        _contains_mod_inv(cmd.args[0])
        for cmd in smt_script
        if cmd.name == "assert"
    ):
        if subaction is not None:
            subaction += {
                "definition_folds": 0,
                "fallback_asserts": 0,
                "fallback_inverse_constraints": 0,
                "fallback_fresh_symbols": 0,
            }
        return smt_script

    declared = {
        cmd.args[0].symbol_name()
        for cmd in smt_script
        if cmd.name == "declare-fun"
    }
    definition_folds = 0
    fallback_asserts = 0
    fallback_constraints = 0
    fallback_fresh_symbols = 0
    output = []
    for cmd in smt_script:
        if cmd.name != "assert":
            output.append(cmd)
            continue

        # --- Strategy 1: definition-level fold ---
        m = _match_mod_inv_definition(cmd.args[0])
        if m is not None:
            definition_folds += 1
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
        rewriter = _FallbackModInvRewriter()
        fallback_asserts += 1
        cmd.args[0] = rewriter.rewrite(cmd.args[0])
        fallback_constraints += len(rewriter.constraints)
        fallback_fresh_symbols += len(rewriter.new_symbols)
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
    if subaction is not None:
        subaction += {
            "definition_folds": definition_folds,
            "fallback_asserts": fallback_asserts,
            "fallback_inverse_constraints": fallback_constraints,
            "fallback_fresh_symbols": fallback_fresh_symbols,
        }
    return smt_script
