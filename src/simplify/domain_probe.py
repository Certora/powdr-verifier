"""SMT-backed strengthening for small finite integer domains (choice/or-eq).

Probes run as one-shot ``z3`` subprocesses on the connected component of the
choice-only assertion slice, not as incremental ``push``/``pop`` on a linked
``Solver``. Two hard-won reasons: (1) under an open push scope z3 weakens its
tactic (``solve-eqs`` cannot eliminate variables) and returns ``unknown`` on the
nonlinear-mod selector goals a fresh one-shot solve discharges in well under a
second; (2) the linked pysmt z3 is older/weaker than the ``z3-nightly`` binary
the rest of the pipeline uses. See src/check/sliced.py for the same lesson.
"""
from __future__ import annotations

import logging
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Optional

from ..report.action import Action
from ..smt.utils import *
from ..utils.args import ARGS
from ..utils.stats import stats_dump

logger = logging.getLogger(__name__)

_MAX_VALUES = 3
# Bound the whole pass so easy solver steps (nothing forced) never pay much: a
# per-probe soft timeout and a total wall-clock budget across all components.
# The useful pins on the hard blocks land in a few seconds each (incremental
# hints make later probes cheap); the wall budget caps the wasted work on blocks
# where nothing is forced.
_PROBE_BUDGET_S = 8
_TOTAL_WALL_S = 20.0
_MAX_COMPONENT_VARS = 40
_MAX_COMPONENT_ASSERTS = 400


def _cluster_assertions(
    assertions: list[FNode], cluster: frozenset[FNode]
) -> list[FNode]:
    return [a for a in assertions if a.get_free_variables() <= cluster]


def _const_pinned_in(f: FNode) -> set[FNode]:
    """Integer symbols fixed to a constant by ``(= v c)`` (recursing into ``and``)."""
    if f.is_equals():
        a, b = f.args()
        if a.is_symbol() and a.get_type().is_int_type() and b.is_int_constant():
            return {a}
        if b.is_symbol() and b.get_type().is_int_type() and a.is_int_constant():
            return {b}
        return set()
    if f.is_and():
        out: set[FNode] = set()
        for arg in f.args():
            out |= _const_pinned_in(arg)
        return out
    return set()


def _const_pinned(assertions: list[FNode]) -> set[FNode]:
    out: set[FNode] = set()
    for a in assertions:
        out |= _const_pinned_in(a)
    return out


def _selector_components(
    assertions: list[FNode],
    choices: dict[FNode, list[int]],
    pinned: set[FNode],
) -> list[frozenset[FNode]]:
    """Connected components of choice symbols linked by *narrow* assertions.

    A narrow assertion is one whose free variables are all either choice symbols
    or constant-pinned auxiliaries (booleanity, one-hot sum, decode-constant
    link). Its choice symbols get unioned. Constant-pinned aux vars (an opcode
    concretized to a literal, a zeroed column) are known values, so pulling them
    and their defining assertions into the slice keeps it self-contained without
    dragging in wide data columns. The component is the self-contained slice that
    forces a selector -- a bare per-row cluster is generally too small.
    """
    choice_syms = set(choices.keys())
    allowed = choice_syms | pinned
    parent: dict[FNode, FNode] = {s: s for s in choice_syms}

    def find(x: FNode) -> FNode:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: FNode, b: FNode) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for a in assertions:
        fvs = a.get_free_variables()
        if not fvs or not fvs <= allowed:
            continue
        cs = [v for v in fvs if v in choice_syms]
        for other in cs[1:]:
            union(cs[0], other)

    groups: dict[FNode, set[FNode]] = {}
    for s in choice_syms:
        groups.setdefault(find(s), set()).add(s)
    return [frozenset(g) for g in groups.values()]


def _component_slice(
    assertions: list[FNode],
    component: frozenset[FNode],
    pinned: set[FNode],
) -> list[FNode]:
    """Narrow assertions touching ``component``, plus the pins for aux vars they use."""
    allowed = set(component) | pinned
    narrow = [
        a
        for a in assertions
        if a.get_free_variables() <= allowed and (a.get_free_variables() & component)
    ]
    used_pinned = {v for a in narrow for v in a.get_free_variables()} & pinned
    aux = [
        a
        for a in assertions
        if a.get_free_variables() and a.get_free_variables() <= used_pinned
    ]
    return narrow + [a for a in aux if a not in narrow]


def _parse_or_equalities(f: FNode) -> Optional[tuple[FNode, tuple[int, ...]]]:
    if not f.is_or():
        return None
    sym: Optional[FNode] = None
    vals: list[int] = []
    for d in f.args():
        if not d.is_equals():
            return None
        a, b = d.args()
        if a.is_symbol() and b.is_int_constant():
            cur_sym, c = a, int(b.constant_value())
        elif b.is_symbol() and a.is_int_constant():
            cur_sym, c = b, int(a.constant_value())
        else:
            return None
        if sym is None:
            sym = cur_sym
        elif sym != cur_sym:
            return None
        vals.append(c)
    if sym is None or not vals:
        return None
    return sym, tuple(sorted(set(vals)))


def _tighten(
    bounds: dict[FNode, tuple[Optional[int], Optional[int]]],
    sym: FNode,
    lo: Optional[int] = None,
    hi: Optional[int] = None,
) -> None:
    clo, chi = bounds.get(sym, (None, None))
    if lo is not None:
        clo = lo if clo is None else max(clo, lo)
    if hi is not None:
        chi = hi if chi is None else min(chi, hi)
    bounds[sym] = (clo, chi)


def _bounds_from_atom(
    f: FNode,
    bounds: dict[FNode, tuple[Optional[int], Optional[int]]],
    negated: bool = False,
) -> None:
    """Collect per-symbol integer bounds from ``<=`` / ``<`` atoms.

    Recurses through top-level ``and`` and ``not``. Disjunctions are ignored
    (they cannot tighten a bound). pysmt normalizes ``>=``/``>`` to swapped
    ``<=``/``<``, so only ``is_le``/``is_lt`` need handling.
    """
    if f.is_not():
        _bounds_from_atom(f.args()[0], bounds, not negated)
        return
    if f.is_and() and not negated:
        for a in f.args():
            _bounds_from_atom(a, bounds, False)
        return
    is_le = f.is_le()
    is_lt = f.is_lt()
    if not (is_le or is_lt):
        return
    a, b = f.args()
    ca = int(a.constant_value()) if a.is_int_constant() else None
    cb = int(b.constant_value()) if b.is_int_constant() else None
    sa = a if (a.is_symbol() and a.get_type().is_int_type()) else None
    sb = b if (b.is_symbol() and b.get_type().is_int_type()) else None
    if not negated:
        # a <= b  (strict: a < b)
        strict = is_lt
        if sa is not None and cb is not None:  # sym <= cb
            _tighten(bounds, sa, hi=cb - 1 if strict else cb)
        if ca is not None and sb is not None:  # ca <= sym
            _tighten(bounds, sb, lo=ca + 1 if strict else ca)
    else:
        # not(a <= b) => a > b ; not(a < b) => a >= b
        strict = is_le  # negated non-strict becomes strict >
        if sa is not None and cb is not None:  # sym > cb
            _tighten(bounds, sa, lo=cb + 1 if strict else cb)
        if ca is not None and sb is not None:  # ca > sym => sym < ca
            _tighten(bounds, sb, hi=ca - 1 if strict else ca)


def _eval_univariate(node: FNode, sym: FNode, v: int) -> int:
    """Evaluate an integer polynomial ``node`` (in the single symbol ``sym``) at ``v``."""
    if node.is_int_constant():
        return int(node.constant_value())
    if node.is_symbol():
        if node == sym:
            return v
        raise ValueError("multi-variable")
    if node.is_plus():
        total = 0
        for a in node.args():
            total += _eval_univariate(a, sym, v)
        return total
    if node.is_times():
        prod = 1
        for a in node.args():
            prod *= _eval_univariate(a, sym, v)
        return prod
    if node.is_minus():
        a, b = node.args()
        return _eval_univariate(a, sym, v) - _eval_univariate(b, sym, v)
    raise ValueError("unhandled node")


def _poly_domain(f: FNode, max_n: int) -> Optional[tuple[FNode, list[int]]]:
    """Small integer roots of a univariate ``(= (mod POLY P) 0)`` domain constraint.

    Selector booleanity survives ``normalize`` as an expanded modular polynomial
    (``x(x-1)(x-2) = 0 mod P`` for a ternary flag), not a range. Root-finding over
    ``[0, max_n]`` recovers the ``{0, 1, 2}`` domain. Only the candidate set matters
    for soundness here -- the forced-value pin is re-confirmed independently -- so a
    missed large root just means no pin, never an unsound one.
    """
    if not f.is_equals():
        return None
    a, b = f.args()
    if a.is_int_constant() and int(a.constant_value()) == 0:
        modn = b
    elif b.is_int_constant() and int(b.constant_value()) == 0:
        modn = a
    else:
        return None
    if not modn.is_mod():
        return None
    poly, div = modn.args()
    if not div.is_int_constant():
        return None
    mod = int(div.constant_value())
    fvs = [
        v
        for v in poly.get_free_variables()
        if v.is_symbol() and v.get_type().is_int_type()
    ]
    if len(fvs) != 1:
        return None
    sym = fvs[0]
    roots: list[int] = []
    for v in range(0, max_n + 1):
        try:
            if _eval_univariate(poly, sym, v) % mod == 0:
                roots.append(v)
        except ValueError:
            return None
    if len(roots) <= 1:
        return None
    return sym, roots


def _poly_choices(
    assertions: list[FNode], max_n: int
) -> dict[FNode, list[int]]:
    out: dict[FNode, list[int]] = {}
    for a in assertions:
        parsed = _poly_domain(a, max_n)
        if parsed is not None:
            sym, roots = parsed
            out.setdefault(sym, roots)
    return out


def _bound_choices(
    assertions: list[FNode], max_n: int
) -> dict[FNode, list[int]]:
    """Symbols whose collected integer bounds pin a small finite domain.

    The field bound (``0 <= v < P``) alone is far larger than ``max_n`` and is
    ignored; a tight range like ``0 <= v <= 2`` intersects it down to a probeable
    domain. Detecting selectors by their domain (rather than by name) is what lets
    a single mechanism cover opcode flags and any other small-domain column.
    """
    bounds: dict[FNode, tuple[Optional[int], Optional[int]]] = {}
    for a in assertions:
        _bounds_from_atom(a, bounds, False)
    out: dict[FNode, list[int]] = {}
    for sym, (lo, hi) in bounds.items():
        if lo is None or hi is None or lo > hi:
            continue
        if 1 < hi - lo + 1 <= max_n:
            out[sym] = list(range(lo, hi + 1))
    return out


def _choices_in_assertion(f: FNode) -> list[tuple[FNode, FNode, tuple[int, ...]]]:
    """Return ``(sym, or_node, values)`` for each choice constraint in ``f``."""
    parsed = _parse_or_equalities(f)
    if parsed is not None:
        sym, vals = parsed
        return [(sym, f, vals)]
    if not f.is_and():
        return []
    or_parts: dict[FNode, tuple[FNode, tuple[int, ...]]] = {}
    for arg in f.args():
        p = _parse_or_equalities(arg)
        if p is not None:
            sym, vals = p
            or_parts[sym] = (arg, vals)
    return [(sym, or_node, vals) for sym, (or_node, vals) in or_parts.items()]


def _collect_choices(assertions: list[FNode], max_n: int) -> dict[FNode, list[int]]:
    """Map each choice variable to probe candidate values (non-singleton, <= max_n)."""
    raw: dict[FNode, list[int]] = {}
    for a in assertions:
        for sym, _, vals in _choices_in_assertion(a):
            if not sym.is_symbol() or not sym.get_type().is_int_type():
                continue
            cur = raw.setdefault(sym, [])
            for v in vals:
                if v not in cur:
                    cur.append(v)
            cur.sort()
    # Range/bound-derived small domains (selectors, booleans, ...): these have no
    # or-of-equalities form, only integer bounds, so they are invisible to the
    # parser above. A symbol seen both ways keeps the union of candidate values;
    # over-approximating the domain only adds probes and is sound either way.
    extra: dict[FNode, list[int]] = {}
    for src in (_bound_choices(assertions, max_n), _poly_choices(assertions, max_n)):
        for sym, vals in src.items():
            cur = extra.setdefault(sym, [])
            for v in vals:
                if v not in cur:
                    cur.append(v)
    for sym, vals in extra.items():
        cur = raw.setdefault(sym, [])
        for v in vals:
            if v not in cur:
                cur.append(v)
        cur.sort()
    return {sym: vals for sym, vals in raw.items() if 1 < len(vals) <= max_n}


def _smt_sort(t) -> str:
    if t.is_bool_type():
        return "Bool"
    if t.is_int_type():
        return "Int"
    if t.is_real_type():
        return "Real"
    return str(t)


def _declare(v: FNode) -> str:
    t = v.symbol_type()
    if t.is_function_type():
        params = " ".join(_smt_sort(p) for p in t.param_types)
        return f"(declare-fun {v.symbol_name()} ({params}) {_smt_sort(t.return_type)})"
    return f"(declare-fun {v.symbol_name()} () {_smt_sort(t)})"


def _oneshot(formulas: list[FNode], budget_s: int) -> Optional[bool]:
    """One-shot ``z3`` subprocess. Returns True=sat, False=unsat, None=unknown."""
    from ..smt_backends.pysmt import solver_command

    solver = solver_command(getattr(ARGS(), "solver", "z3-nightly"), "domain_probe")
    if solver is None:
        return None
    decls = sorted(
        {v for f in formulas for v in f.get_free_variables()},
        key=lambda v: v.symbol_name(),
    )
    lines = ["(set-logic ALL)"]
    lines += [_declare(v) for v in decls]
    lines += [f"(assert {f.to_smtlib(daggify=True)})" for f in formulas]
    lines.append("(check-sat)")
    fd, name = tempfile.mkstemp(suffix=".smt2")
    os.close(fd)
    path = Path(name)
    try:
        path.write_text("\n".join(lines) + "\n")
        proc = subprocess.run(
            [solver, f"-T:{budget_s}", "smt.random_seed=0", "sat.random_seed=0", str(path)],
            capture_output=True,
            text=True,
            timeout=budget_s + 5,
        )
        out = proc.stdout
        if re.search(r"^unsat", out, re.M):
            return False
        if re.search(r"^sat", out, re.M):
            return True
        return None
    except (subprocess.TimeoutExpired, OSError) as e:
        logger.info("domain_probe: probe subprocess error: %s", e)
        return None
    finally:
        try:
            path.unlink()
        except OSError:
            pass


def _probe_component(
    rel: list[FNode],
    component_choices: dict[FNode, list[int]],
    batch: list[FNode],
    deadline: float,
) -> dict[str, int]:
    """Probe each selector's candidate values against the component slice ``rel``.

    Proven exclusions and pins accumulate in ``extra`` and feed back into later
    probes of the same component (an earlier pin often makes a later one cheap).
    Only forced-value *pins* are emitted to ``batch``: they get substituted by the
    downstream ``z3-propagate-values`` and collapse the selector-gated cubics.
    Exclusions are kept only as internal hints -- emitting the ``(not (= v c))``
    inequalities would perturb otherwise-easy formulas without collapsing anything.
    Every emitted pin is still entailed by ``rel`` (a subset of the assertions),
    so the exclusion hints, themselves ``rel``-entailed, do not affect soundness.
    """
    outcomes = {
        "probes_sat": 0,
        "probes_unsat": 0,
        "probes_unknown": 0,
        "pinned": 0,
    }
    extra: list[FNode] = []
    for sym, vals in sorted(component_choices.items(), key=lambda kv: str(kv[0])):
        if time.monotonic() > deadline:
            break
        sat_vals: list[int] = []
        unsat_vals: list[int] = []
        for v in vals:
            if time.monotonic() > deadline:
                break
            eq = Equals(sym, Int(v))
            r = _oneshot(rel + extra + [eq], _PROBE_BUDGET_S)
            tag = {True: "sat", False: "unsat", None: "unknown"}[r]
            logger.info("domain_probe: probe (= %s %s) -> %s", sym, v, tag)
            if tag == "sat":
                outcomes["probes_sat"] += 1
                sat_vals.append(v)
            elif tag == "unsat":
                outcomes["probes_unsat"] += 1
                unsat_vals.append(v)
                extra.append(Not(eq))  # internal hint only
            else:
                outcomes["probes_unknown"] += 1
        # Forced value: every candidate but one refuted. The surviving value is
        # then entailed by the slice -- confirm it directly (refute sym != v) so
        # soundness never relies on the probed domain being exhaustive, and emit
        # the equality.
        if (
            len(sat_vals) == 1
            and len(unsat_vals) == len(vals) - 1
            and time.monotonic() <= deadline
        ):
            survivor = sat_vals[0]
            eqp = Equals(sym, Int(survivor))
            if eqp not in batch and _oneshot(rel + extra + [Not(eqp)], _PROBE_BUDGET_S) is False:
                batch.append(eqp)
                extra.append(eqp)
                outcomes["pinned"] += 1
                logger.info("domain_probe: pin -> assert %s", eqp)
    return outcomes


def simplify_domain_probe(
    smt_script: script.SmtLibScript,
    subaction: Action,
) -> script.SmtLibScript:
    total_added = 0
    assertions = [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]
    probe_stats: dict = {"base_asserts": len(assertions)}

    if not assertions:
        stats_dump("domain_probe", probe_stats)
        return smt_script

    choices = _collect_choices(assertions, _MAX_VALUES)
    probe_stats["choice_symbols"] = len(choices)
    if not choices:
        probe_stats.update({"pairs_probed": 0, "clusters_probed": 0})
        stats_dump("domain_probe", probe_stats)
        return smt_script

    try:
        insert_at = next(
            (i for i, c in enumerate(smt_script.commands) if c.name == "check-sat"),
            len(smt_script.commands),
        )
        pinned = _const_pinned(assertions)
        components = _selector_components(assertions, choices, pinned)
        # Probe smaller components first: they resolve fast and their pins can
        # feed the field bound / opcode-decode context for the larger ones.
        components.sort(key=len)
        symbols_probed = 0
        clusters_probed = 0
        flag_vars_total = 0
        flag_local_total = 0
        deadline = time.monotonic() + _TOTAL_WALL_S

        logger.info(
            "domain_probe: start (%d base asserts, %d candidate(s), %d component(s))",
            len(assertions),
            len(choices),
            len(components),
        )

        batch: list[FNode] = []
        cluster_stats: list[dict] = []
        for cluster in components:
            if time.monotonic() > deadline:
                logger.info("domain_probe: wall budget exhausted, stopping")
                break
            component_choices = {s: choices[s] for s in cluster if s in choices}
            if not component_choices:
                continue

            rel = _component_slice(assertions, cluster, pinned)
            if len(cluster) > _MAX_COMPONENT_VARS or len(rel) > _MAX_COMPONENT_ASSERTS:
                logger.info(
                    "domain_probe: skip component (%d flag var(s), %d assert(s))",
                    len(cluster),
                    len(rel),
                )
                continue
            clusters_probed += 1
            symbols_probed += len(component_choices)
            flag_vars_total += len(cluster)
            flag_local_total = len(rel)

            logger.info(
                "domain_probe: component %d vars %s (%d assert(s))",
                clusters_probed,
                sorted(map(str, cluster)),
                len(rel),
            )

            cluster_outcomes = _probe_component(rel, component_choices, batch, deadline)
            cluster_stats.append({
                "index": clusters_probed,
                "n_vars": len(component_choices),
                "n_flag_vars": len(cluster),
                "n_asserts": len(rel),
                **cluster_outcomes,
            })

        probe_stats.update({
            "pairs_probed": symbols_probed,
            "clusters_probed": clusters_probed,
            "flag_vars": flag_vars_total,
            "flag_local_asserts": flag_local_total,
            "clusters": cluster_stats,
        })

        if batch:
            for f in batch:
                smt_script.commands.insert(
                    insert_at,
                    script.SmtLibCommand(name="assert", args=[f]),
                )
                insert_at += 1
            total_added += len(batch)
            logger.info("domain_probe: inserted %d assert(s)", len(batch))
        else:
            logger.info("domain_probe: no new facts")

        logger.info(
            "domain_probe: done (%d new assert(s) in script)",
            total_added,
        )
        return smt_script
    except Exception as e:
        logger.info("domain_probe: solver error, stopping: %s", e)
        return smt_script
    finally:
        probe_stats["added_facts"] = total_added
        stats_dump("domain_probe", probe_stats)
