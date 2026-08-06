import time
from io import StringIO
from pathlib import Path
from textwrap import dedent

import pytest
from pysmt.environment import pop_env, push_env

from src.simplify.nnf import NNFConverter, simplify_nnf
from src.smt.utils import *


@pytest.fixture(autouse=True)
def _isolated_pysmt_env():
    """Give each test its own pysmt environment.

    pysmt keeps one global symbol table, so a symbol declared with a different sort
    by any earlier test in the session makes the parses here fail with "Trying to
    redefine symbol 'q' with a new type" -- these tests pass alone and fail in the
    full run. ``push_env``/``pop_env`` rather than ``reset_env`` so the surrounding
    environment is restored afterwards and nothing leaks the other way either.
    """
    push_env()
    try:
        yield
    finally:
        pop_env()


def _parse(script_text: str) -> script.SmtLibScript:
    return SmtLibParser().get_script(StringIO(dedent(script_text).strip() + "\n"))


def _assert_nnf(formula: FNode) -> None:
    assert not formula.is_implies()

    def walk(f: FNode) -> None:
        if f.is_not():
            inner = f.arg(0)
            assert not inner.is_not()
            assert not inner.is_and()
            assert not inner.is_or()
            assert not inner.is_implies()
        for a in f.args():
            walk(a)

    walk(formula)


def test_nnf_converter():
    x, y, z = Symbol("x", INT), Symbol("y", INT), Symbol("z", INT)
    p, q, r = Symbol("p", BOOL), Symbol("q", BOOL), Symbol("r", BOOL)
    formulas = [
        Implies(p, q),
        Implies(And(p, q), Or(r, Not(q))),
        Not(And(Implies(p, q), Or(Not(p), r))),
        ForAll([x], Implies(Equals(x, Int(0)), Equals(y, z))),
        And(
            Implies(p, q),
            Implies(Or(p, q), r),
            Not(Or(And(p, q), Not(r))),
        ),
    ]
    for formula in formulas:
        nnf = NNFConverter().substitute(formula)
        _assert_nnf(nnf)


def test_simplify_nnf_script():
    smt_script = _parse(
        """
        (set-logic ALL)
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assert (=> p q))
        (assert (= p p))
        (check-sat)
        """
    )
    simplified = simplify_nnf(smt_script)
    asserts = [cmd.args[0] for cmd in simplified if cmd.name == "assert"]
    assert asserts[0] == Or(Not(Symbol("p", BOOL)), Symbol("q", BOOL))
    assert asserts[1] == Equals(Symbol("p", BOOL), Symbol("p", BOOL))


def test_nnf_on_guest_keccak_soundness():
    path = Path(
        "data/guest-keccak/"
        "verify-apc_candidate_2106368_001_exec_bus-apc_candidate_2106368_002_loop_iteration.soundness.smt2"
    )
    if not path.exists():
        return
    with open(path) as fh:
        root = next(
            cmd.args[0]
            for cmd in SmtLibParser().get_script(fh).commands
            if cmd.name == "assert"
        )
    t0 = time.perf_counter()
    nnf = NNFConverter().substitute(root)
    elapsed = time.perf_counter() - t0
    _assert_nnf(nnf)
    assert elapsed < 3.0
