import z3

from src.smt.utils import *
from src.simplify.z3 import _is_shared_array_pin, simplify_z3


def test_is_shared_array_pin():
    before = Symbol("before-memory-0-mult", INT)
    after = Symbol("after-memory-0-mult", INT)
    assert _is_shared_array_pin(Equals(before, after))
    assert not _is_shared_array_pin(Equals(before, Int(0)))


def _script_with_check_sat(commands):
    smt_script = script.SmtLibScript()
    smt_script.commands = list(commands) + [script.SmtLibCommand("check-sat", [])]
    return smt_script


def test_z3_simplify_folds_not_equal_constants():
    x = Symbol("x", INT)
    smt_script = _script_with_check_sat(
        [
            script.SmtLibCommand("declare-fun", [x, INT]),
            script.SmtLibCommand(
                "assert",
                [Or(Not(Equals(Int(0), Int(0))), Equals(x, Int(1)))],
            ),
        ]
    )
    out = simplify_z3(smt_script, ["simplify"])
    assert_cmds = [c for c in out.commands if c.name == "assert"]
    assert assert_cmds[-1].args[0] == Equals(x, Int(1))


def test_z3_simplify_preserves_mod_shape():
    x = Symbol("x", INT)
    p = Int(2013265921)
    inner = Not(Equals(Mod(Times(x, Int(2)), p), Int(0)))
    smt_script = _script_with_check_sat(
        [
            script.SmtLibCommand("declare-fun", [x, INT]),
            script.SmtLibCommand("assert", [inner]),
        ]
    )
    out = simplify_z3(smt_script, ["simplify"])
    assert_cmds = [c for c in out.commands if c.name == "assert"]
    out_f = assert_cmds[-1].args[0]
    assert out_f.is_not() and out_f.arg(0).is_equals()
    eq = out_f.arg(0)
    lhs, rhs = eq.args()
    assert lhs.is_mod() and rhs.is_int_constant(0)
    mod_e, mod_m = lhs.args()
    assert mod_m == p and mod_e.get_free_variables() == {x}


def test_z3_propagate_preserves_shared_array_pins():
    before = Symbol("before-memory-0-data0", INT)
    after = Symbol("after-memory-0-data0", INT)
    x = Symbol("before-a__0_0@1", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [before, INT]),
        script.SmtLibCommand("declare-fun", [after, INT]),
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(0))]),
        script.SmtLibCommand("assert", [Equals(before, after)]),
        script.SmtLibCommand("check-sat", []),
    ]
    out = simplify_z3(smt_script, ["propagate-values"])
    pin_cmds = [
        cmd
        for cmd in out.commands
        if cmd.name == "assert" and cmd.args[0].is_equals()
        and _is_shared_array_pin(cmd.args[0])
    ]
    assert len(pin_cmds) == 1
    assert pin_cmds[0].args[0] == Equals(before, after)


def test_z3_solve_eqs():
    a = z3.Int('a')
    b = z3.Int('b')
    f = a == b*b - 3

    tactic = z3.Then('simplify', 'solve-eqs')
    goal = z3.Goal()
    goal.add(f)
    result = tactic(goal)
    print(f'result: {result}')

    s = z3.Solver()
    s.add(result[0])
    print(f'check: {s.check()}')
    print(f'model: {s.model()}')
    print(result[0].convert_model(s.model()))

    #import IPython; IPython.embed()

    #s = z3.Solver()
    #for r in result:
    #    s.add(r)
    #s.check()
    #model = s.model()
    #print(f'model: {model}')

    #print(goal.convert_model(model))
