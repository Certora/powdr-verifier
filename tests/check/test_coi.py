import re

from src.check.coi import ConstraintIndex, boundary_vars
from src.smt.utils import *

BOUNDARY_RE = re.compile(r"memory_(match|isinput|isoutput|isdisabled)")


def _sym(name):
    return Symbol(name, INT)


def _bool(name):
    return Symbol(name, BOOL)


def _setup():
    """Small constraint set with an arithmetic chain, a boundary bridge, and
    a memory-only region.

    0: x = 1                      (arith, x)
    1: y = x + 1                  (arith, x-y)
    2: z = 5                      (arith, disconnected from x/y)
    3: memory_match_a -> y = 2    (bridge: boundary + arith var)
    4: memory_match_a | memory_match_b   (memory-only)
    5: !memory_match_b            (memory-only)
    """
    x, y, z = _sym("x"), _sym("y"), _sym("z")
    ma, mb = _bool("memory_match_a"), _bool("memory_match_b")
    constraints = [
        Equals(x, Int(1)),
        Equals(y, Plus(x, Int(1))),
        Equals(z, Int(5)),
        Implies(ma, Equals(y, Int(2))),
        Or(ma, mb),
        Not(mb),
    ]
    boundary = boundary_vars(constraints, BOUNDARY_RE)
    return constraints, boundary, ConstraintIndex(constraints, boundary)


def test_boundary_vars_regex():
    constraints, boundary, _ = _setup()
    assert boundary == {_bool("memory_match_a"), _bool("memory_match_b")}


def test_mem_indices_touch_boundary():
    _, _, index = _setup()
    assert index.mem_indices == {3, 4, 5}


def test_slice_stops_at_boundary():
    """Seeding from x picks the arith chain and the bridge constraint (it
    touches y), but does NOT expand through memory_match_a into the
    memory-only region."""
    _, _, index = _setup()
    sl = index.slice_indices({_sym("x")})
    assert sl == {0, 1, 3}


def test_slice_disconnected_component_excluded():
    _, _, index = _setup()
    assert index.slice_indices({_sym("z")}) == {2}


def test_pure_boundary_seed_is_empty_slice():
    """A seed of only boundary vars never expands: the memory-only disjuncts."""
    _, _, index = _setup()
    assert index.slice_indices({_bool("memory_match_a"), _bool("memory_match_b")}) == frozenset()


def test_slice_seed_ignores_boundary_vars():
    """slice_seed is a complete cache key: boundary seed vars don't matter."""
    _, _, index = _setup()
    d1 = And(Equals(_sym("x"), Int(3)), _bool("memory_match_a"))
    d2 = Equals(_sym("x"), Int(4))
    assert index.slice_seed(d1) == index.slice_seed(d2) == {_sym("x")}
    assert index.slice_indices(index.slice_seed(d1)) == index.slice_indices({_sym("x")})


def test_no_boundary_full_coi():
    """With an empty boundary the fixpoint is plain COI over connectivity."""
    constraints, _, _ = _setup()
    index = ConstraintIndex(constraints, frozenset())
    sl = index.slice_indices({_sym("x")})
    # x -> {0,1}, y -> bridge 3, memory_match_a -> {4}, memory_match_b -> {5}
    assert sl == {0, 1, 3, 4, 5}
