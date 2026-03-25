"""Unit tests for `IntVarDomains` (variable maps to `IntDomain`)."""

from src.simplify.intervals.domain import IntDomain, IntInterval, IntVarDomains


def iv(lo: int | None, hi: int | None) -> IntInterval:
    return IntInterval(lo, hi)


def test_top_bottom_singleton():
    t = IntVarDomains.top()
    assert t.is_top()
    assert not t.is_bottom()
    assert t.to_dict() == {}
    assert t.get("x") == IntDomain.top()

    b = IntVarDomains.bottom()
    assert b.is_bottom()
    assert not b.is_top()
    assert b.get("x") == IntDomain.bottom()

    s = IntVarDomains.singleton("x", IntDomain.const(3))
    assert s.get("x") == IntDomain.const(3)
    assert s.get("y") == IntDomain.top()


def test_from_mapping_drops_top_and_detects_bottom():
    a = IntVarDomains.from_mapping(
        {
            "x": IntDomain.from_interval(iv(1, 5)),
            "y": IntDomain.top(),
        }
    )
    assert set(a.to_dict()) == {"x"}
    assert a.get("y") == IntDomain.top()

    b = IntVarDomains.from_mapping({"x": IntDomain.bottom()})
    assert b.is_bottom()


def test_to_dict_returns_copy():
    env = IntVarDomains.singleton("x", IntDomain.const(1))
    d = env.to_dict()
    d["x"] = IntDomain.const(99)
    assert env.get("x") == IntDomain.const(1)


def test_eq():
    assert IntVarDomains.top() == IntVarDomains.from_mapping({})
    assert IntVarDomains.bottom() == IntVarDomains.bottom()
    a = IntVarDomains({"x": IntDomain.from_interval(iv(0, 1))})
    b = IntVarDomains({"x": IntDomain.from_interval(iv(0, 1))})
    assert a == b
    assert a != IntVarDomains.top()


def test_intersect_meet():
    a = IntVarDomains(
        {
            "x": IntDomain.from_interval(iv(1, 10)),
            "y": IntDomain.const(0),
        }
    )
    b = IntVarDomains({"x": IntDomain.from_interval(iv(5, 20))})
    m = a.intersect(b)
    assert m.get("x") == IntDomain.from_interval(iv(5, 10))
    assert m.get("y") == IntDomain.const(0)

    disjoint = IntVarDomains({"x": IntDomain.from_interval(iv(0, 1))}).intersect(
        IntVarDomains({"x": IntDomain.from_interval(iv(3, 4))})
    )
    assert disjoint.is_bottom()


def test_intersect_with_bottom():
    x = IntVarDomains.singleton("x", IntDomain.const(1))
    assert x.intersect(IntVarDomains.bottom()).is_bottom()
    assert IntVarDomains.bottom().intersect(x).is_bottom()


def test_union_join_hull():
    u = IntVarDomains({"x": IntDomain.from_interval(iv(1, 2))}).union(
        IntVarDomains({"x": IntDomain.from_interval(iv(4, 5))})
    )
    assert u.get("x") == IntDomain.from_interval(iv(1, 5))


def test_union_missing_variable_is_top_on_other_side():
    """Join uses top for absent keys, so one-sided info is widened to top."""
    u = IntVarDomains.singleton("x", IntDomain.const(1)).union(IntVarDomains.top())
    assert u.is_top()


def test_union_bottom_is_identity_for_join():
    assert IntVarDomains.bottom().union(IntVarDomains.top()) == IntVarDomains.top()
    only_x = IntVarDomains.singleton("x", IntDomain.from_interval(iv(0, 2)))
    assert IntVarDomains.bottom().union(only_x) == only_x
    assert only_x.union(IntVarDomains.bottom()) == only_x
