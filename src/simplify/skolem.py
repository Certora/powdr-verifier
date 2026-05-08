"""Unified skolem-map simplifier.

This pass replaces the verifier-side ``ModelMapBuilder`` and the previous
per-pass skolem injectors. Instead of letting multiple passes append
disjuncts independently, the pass builds a single :class:`SkolemMap`
per ``forall`` and runs a fixed sequence of *contributors* against it.
Each contributor sees what is already pinned, so a more specific
witness wins over a less specific one without anyone having to grep
the body for existing skolem equalities.

This module owns the orchestrator and the shared :class:`SkolemMap`
container; the (de)serialization helpers used by the contributors live
in :mod:`.skolem_utils`.

Each *contributor* lives in its own module:

  1. :mod:`.skolem_rules`    - OpenVM ``EqualZeroCheck``.
  2. :mod:`.skolem_derived`  - eliminations / derived-column pins
     (verifier emits ``:skolem-derived-N`` set-info entries).
  3. :mod:`.skolem_pclookup` - pc-lookup pre-resolved pins (verifier
     emits ``:skolem-pclookup-N`` set-info entries; resolution has to
     happen at encode time because it uses the encoder's incremental
     constraint solver).
  4. :mod:`.skolem_names`    - same-name fallback.

For every ``forall`` whose body is an ``Or`` (post-NNF) we build a
fresh :class:`SkolemMap` over its qvars and run the contributors in
the order above (most-specific to least-specific so the first three
win over the same-name fallback; within a contributor, the first pin
for a qvar is kept). Every pinned qvar is appended to the body as
``Not(q = wrap_mod(expr))`` (or ``Not(q = expr)`` for non-int types);
``simplify_lift_forall`` later hoists each disjunct to a top-level
assertion, removing ``q`` from the universal.
"""

from ..smt.utils import *
from ..smt_backends.pysmt import wrap_mod

from . import skolem_derived, skolem_names, skolem_pclookup, skolem_rules


class SkolemMap:
    """Per-forall pin collector.

    Tracks ``{qvar -> witness expr}`` plus a tag identifying which
    contributor pinned each qvar (used for logging / debugging only).
    The first contributor wins; later :meth:`pin` calls for the same
    qvar are silently dropped.
    """

    def __init__(self, qvars):
        self.qvars: frozenset[FNode] = frozenset(qvars)
        self.pins: dict[FNode, FNode] = {}
        self.sources: dict[FNode, str] = {}

    def pin(self, q: FNode, expr: FNode, *, source: str) -> bool:
        """Pin ``q`` to ``expr``. Returns ``True`` if newly pinned."""
        if q not in self.qvars:
            return False
        if q in self.pins:
            return False
        self.pins[q] = expr
        self.sources[q] = source
        return True

    def is_pinned(self, q: FNode) -> bool:
        return q in self.pins

    def emit_disjuncts(self) -> list[FNode]:
        """Materialize the pinned witnesses as ``Not(q = expr)`` disjuncts.

        ``wrap_mod`` is applied only to integer-typed witnesses, in line
        with how ``ModelMapBuilder.get_map`` used to encode them. Non-int
        types (booleans, arrays) are emitted verbatim.
        """
        out = []
        for q, expr in self.pins.items():
            rhs = wrap_mod(expr) if q.get_type().is_int_type() else expr
            out.append(Not(Equals(q, rhs)))
        return out


class _SkolemWalker(IdentityDagWalker):
    """Walk every ``forall`` and append the contributor-built pins."""

    def __init__(
        self,
        declared: dict[str, FNode],
        derived: list[FNode],
        pclookup: list[FNode],
        *args,
        **kwargs,
    ):
        super().__init__(*args, **kwargs)
        self.declared = declared
        self.derived = derived
        self.pclookup = pclookup
        self.applied: dict[str, int] = {}

    def walk_forall(self, formula, args, **kwargs):
        body = args[0]
        if not body.is_or():
            return formula
        qvars = list(formula.quantifier_vars())
        m = SkolemMap(qvars)

        skolem_rules.contribute(m, body)
        skolem_derived.contribute(m, self.derived)
        skolem_pclookup.contribute(m, self.pclookup)
        skolem_names.contribute(m, self.declared)

        for src in m.sources.values():
            self.applied[src] = self.applied.get(src, 0) + 1

        new_disjuncts = m.emit_disjuncts()
        if not new_disjuncts:
            return formula
        return ForAll(qvars, Or(*body.args(), *new_disjuncts))


def simplify_skolem(smt_script: script.SmtLibScript) -> script.SmtLibScript:
    """Append skolem-map disjuncts to every disjunctive ``forall`` body.

    See the module docstring for the full reasoning. The pass is a no-op
    on forall nodes whose body is not a disjunction (run after ``nnf``).
    Must run before ``simplify_lift_forall``.
    """
    declared = skolem_names.collect_declared_symbols(smt_script)
    derived = skolem_derived.collect_pins(smt_script)
    pclookup = skolem_pclookup.collect_pins(smt_script)

    w = _SkolemWalker(declared, derived, pclookup, env=get_env())
    for cmd in smt_script:
        if cmd.name == "assert":
            cmd.args[0] = keep_comment(w.walk(cmd.args[0]), cmd.args[0])

    if w.applied:
        parts = ", ".join(f"{k}={v}" for k, v in sorted(w.applied.items()))
        logging.info(f"skolem: applied {parts}")
    return smt_script
