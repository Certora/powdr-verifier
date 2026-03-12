from src.simplify.intervals import IntInterval


def test_top_and_const():
    assert IntInterval.top() == IntInterval(None, None)
    assert IntInterval.const(7) == IntInterval(7, 7)


def test_is_bottom():
    assert IntInterval(3, 2).is_bottom()
    assert not IntInterval(2, 2).is_bottom()
    # Unbounded sides are never bottom by this representation.
    assert not IntInterval(None, 2).is_bottom()
    assert not IntInterval(3, None).is_bottom()


def test_intersect():
    assert IntInterval(0, 10).intersect(IntInterval(5, 20)) == IntInterval(5, 10)
    assert IntInterval(None, 10).intersect(IntInterval(5, None)) == IntInterval(5, 10)
    assert IntInterval(None, None).intersect(IntInterval(1, 2)) == IntInterval(1, 2)
    # Disjoint intersection produces bottom interval.
    assert IntInterval(0, 1).intersect(IntInterval(3, 4)).is_bottom()


def test_add():
    assert IntInterval(1, 3).add(IntInterval(4, 6)) == IntInterval(5, 9)
    assert IntInterval(None, 3).add(IntInterval(4, 6)) == IntInterval(None, 9)
    assert IntInterval(1, None).add(IntInterval(4, 6)) == IntInterval(5, None)
    assert IntInterval(None, None).add(IntInterval(4, 6)) == IntInterval(None, None)


def test_neg_and_sub():
    assert IntInterval(2, 5).neg() == IntInterval(-5, -2)
    assert IntInterval(None, 5).neg() == IntInterval(-5, None)
    assert IntInterval(2, None).neg() == IntInterval(None, -2)
    assert IntInterval(None, None).neg() == IntInterval(None, None)

    a = IntInterval(10, 20)
    b = IntInterval(3, 5)
    assert a.sub(b) == IntInterval(5, 17)
    # Sanity: sub equals add(neg)
    assert a.sub(b) == a.add(b.neg())


def test_mul():
    assert IntInterval(2, 3).mul(IntInterval(4, 5)) == IntInterval(8, 15)
    assert IntInterval(-2, 3).mul(IntInterval(4, 5)) == IntInterval(-10, 15)
    assert IntInterval(-2, 3).mul(IntInterval(-5, -4)) == IntInterval(-15, 10)
    assert IntInterval(-2, 2).mul(IntInterval(-3, 3)) == IntInterval(-6, 6)
    # Unbounded input falls back to top.
    assert IntInterval(None, 2).mul(IntInterval(1, 3)) == IntInterval.top()
    assert IntInterval(1, 3).mul(IntInterval(None, 2)) == IntInterval.top()


def test_scale():
    assert IntInterval(2, 5).scale(0) == IntInterval.const(0)
    assert IntInterval(2, 5).scale(3) == IntInterval(6, 15)
    assert IntInterval(2, 5).scale(-2) == IntInterval(-10, -4)
    assert IntInterval(None, 5).scale(2) == IntInterval(None, 10)
    assert IntInterval(2, None).scale(-2) == IntInterval(None, -4)


def test_within_0_p():
    p = 11
    assert IntInterval(0, 10).within_0_p(p)
    assert IntInterval(0, 0).within_0_p(p)
    assert not IntInterval(-1, 10).within_0_p(p)
    assert not IntInterval(0, 11).within_0_p(p)  # upper bound is strict (< p)
    assert not IntInterval(None, 10).within_0_p(p)
    assert not IntInterval(0, None).within_0_p(p)


def test_within_open_pm_p():
    p = 11
    assert IntInterval(-10, 10).within_open_pm_p(p)
    assert IntInterval(0, 0).within_open_pm_p(p)
    assert not IntInterval(-11, 10).within_open_pm_p(p)  # lower bound is strict (> -p)
    assert not IntInterval(-10, 11).within_open_pm_p(p)  # upper bound is strict (< p)
    assert not IntInterval(None, 10).within_open_pm_p(p)
    assert not IntInterval(-10, None).within_open_pm_p(p)

