from src.simplify.normalize_eqs import simplify_normalize_eqs, _content_divide
from src.smt.utils import *

# Small prime modulus; the pass reads the modulus from the Mod node, not ARGS.
P = 97


def _script(*asserts):
    smt_script = script.SmtLibScript()
    smt_script.commands = [script.SmtLibCommand("assert", [f]) for f in asserts]
    return smt_script


def _asserts(smt_script):
    return [cmd.args[0] for cmd in smt_script if cmd.name == "assert"]


def test_divides_modular_eq_by_coprime_content():
    x = Symbol("x", INT)
    # 6x + 12 ≡ 0 (mod 97); content 6 is coprime to 97 -> x + 2 ≡ 0
    scaled = Equals(Mod(Plus(Times(Int(6), x), Int(12)), Int(P)), Int(0))
    divided = Equals(Mod(Plus(x, Int(2)), Int(P)), Int(0))
    assert _asserts(simplify_normalize_eqs(_script(scaled))) == [divided]


def test_symmetrizes_before_dividing():
    # coeff 91 = 97 - 6 -> symmetric -6; with 6 and 30, content is 6.
    # -6x + 6y + 30  ->  -x + y + 5
    x = Symbol("x", INT)
    y = Symbol("y", INT)
    t = Plus(Times(Int(91), x), Times(Int(6), y), Int(30))
    out = _content_divide(t, P)
    assert out == Plus(Times(Int(-1), x), y, Int(5))


def test_divides_inside_or_and_not():
    # The hypothesis shape: equalities buried in an Or must still be divided.
    x = Symbol("x", INT)
    f2 = Equals(Mod(Plus(Times(Int(6), x), Int(13)), Int(P)), Int(0))  # content 1
    scaled = Equals(Mod(Plus(Times(Int(6), x), Int(12)), Int(P)), Int(0))
    divided = Equals(Mod(Plus(x, Int(2)), Int(P)), Int(0))
    out = _asserts(simplify_normalize_eqs(_script(Not(Or(scaled, f2)))))
    assert out == [Not(Or(divided, f2))]


def test_coprime_guard_blocks_unsound_division():
    # modulus 6 (non-unit content): 4x + 2 ≡ 0 (mod 6), gcd(4,2)=2 shares a
    # factor with 6, so dividing is unsound -> leave unchanged.
    x = Symbol("x", INT)
    f = Equals(Mod(Plus(Times(Int(4), x), Int(2)), Int(6)), Int(0))
    assert _asserts(simplify_normalize_eqs(_script(f))) == [f]


def test_no_op_when_content_is_one():
    x = Symbol("x", INT)
    f = Equals(Mod(Plus(x, Int(1)), Int(P)), Int(0))
    assert _asserts(simplify_normalize_eqs(_script(f))) == [f]
