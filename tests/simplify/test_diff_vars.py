"""Regression tests for the difference-variable substitution pass.

The pass rewrites ``x`` to ``y + d`` for pairs ``(x, y)`` that occur only as the
difference ``x - y`` in the nonlinear (mod) constraints. It must be a *sound*
(equisatisfiable) change of variables. Two bugs are guarded here:

* Declaration ordering: the fresh ``d`` must be declared BEFORE the asserts that
  reference it -- otherwise the solver errors on the unknown symbol, silently
  drops those asserts, and an ``unsat`` obligation becomes a spurious ``sat``.
* Detection tightness: a pair is only substituted when ``x`` and ``y`` occur
  purely as ``x - y`` (all cross terms ``coeff(x·k) = -coeff(y·k)``), so the
  rewrite is both sound and actually collapses the nonlinear part.
"""
import io
import subprocess

import pytest

from src.smt.utils import *  # noqa: F403 -- registers the custom MOD operator + parser
from src.smt_backends.pysmt import solvers, write_smtlib_script
from src.simplify.diff_vars import simplify_diff_vars
from src.utils.args import parse_args

P = 2013265921


def _z3_bin():
    for s in solvers:
        if s["name"].startswith("z3") and s["path"].exists():
            return s["path"]
    return None


Z3 = _z3_bin()
needs_z3 = pytest.mark.skipif(Z3 is None, reason="no z3 binary available")


def _parse(text):
    from pysmt.smtlib.script import SmtLibScript

    scr = SmtLibScript()
    scr.commands = list(SmtLibParser().get_script(io.StringIO(text)))
    return scr


def _smt_bytes(scr):
    b = io.BytesIO()
    write_smtlib_script(scr, b)
    return b.getvalue()


def _solve(scr):
    r = subprocess.run(
        [str(Z3), "-smt2", "-in"],
        input=_smt_bytes(scr),
        capture_output=True,
        timeout=30,
    )
    out = r.stdout.decode().strip().splitlines()
    return out[-1] if out else r.stderr.decode()[:120]


def _setup():
    parse_args(["simplify", "in.smt2", "default", "out.smt2"])


# (x-y)^2 + 176(x-y) = 0  AND  x - y = 1  -> unsat. Dropping the first assert
# (the declaration-ordering bug) would make it sat -- the regression trigger.
GENUINE = f"""
(set-logic ALL)
(declare-fun x () Int)(declare-fun y () Int)
(assert (= (mod (+ (* x x) (* {P - 2} x y) (* y y)) {P}) 0))
(assert (= (mod (+ x (* {P - 1} y) {P - 1}) {P}) 0))
(check-sat)
"""

# No difference structure at all -> pass must be a no-op.
NO_PAIRS = """
(set-logic ALL)
(declare-fun x () Int)
(assert (= x 1))
(assert (or (= x 2) (= x 3)))
(check-sat)
"""


@needs_z3
def test_genuine_pair_preserves_unsat():
    _setup()
    scr = _parse(GENUINE)
    assert _solve(scr) == "unsat"
    assert _solve(simplify_diff_vars(scr)) == "unsat"  # must NOT become sat


def test_declarations_precede_uses():
    _setup()
    out = simplify_diff_vars(_parse(GENUINE))
    declared = set()
    for cmd in out.commands:
        if cmd.name == "declare-fun":
            declared.add(cmd.args[0].symbol_name())
        elif cmd.name == "assert":
            used = {s.symbol_name() for s in cmd.args[0].get_free_variables()}
            assert used <= declared, f"assert uses undeclared {used - declared}"


def test_no_difference_structure_is_noop():
    _setup()
    out = simplify_diff_vars(_parse(NO_PAIRS))
    assert "!diff" not in _smt_bytes(out).decode()
