"""Unit tests for structure-keyed strategy routing in the sliced checker."""
from src.utils.args import parse_args
from src.check.sliced import Metrics, _ClassRouter, _structure_key
from src.smt.utils import *

UF_XOR = Symbol("uf_xor", FunctionType(INT, [INT, INT]))


def setup_module(_):
    parse_args(["check", "x"])


def _sym(n):
    return Symbol(n, INT)


class TestStructureKey:
    def test_plain_arith_is_unrouted(self):
        d = LT(Plus(_sym("a"), Int(3)), Int(8))
        assert _structure_key(d) is None

    def test_uf_on_columns(self):
        d = Equals(Function(UF_XOR, [_sym("x"), _sym("y")]), _sym("z"))
        assert _structure_key(d) == ("uf",)

    def test_uf_composite_arg(self):
        arg = Plus(_sym("x"), Times(Int(2013265921), _sym("q")))
        d = Equals(Function(UF_XOR, [arg, _sym("y")]), _sym("z"))
        assert _structure_key(d) == ("uf", "ufc")

    def test_mod_witness_marker(self):
        d = Equals(Plus(_sym("a"), Times(Int(7), Symbol("mod!42", INT))), Int(0))
        assert _structure_key(d) == ("modw",)


class TestClassRouter:
    def _router(self):
        return _ClassRouter(Metrics())

    def test_no_route_before_win(self):
        r = self._router()
        assert r.route(("uf",)) is None

    def test_routes_after_win(self):
        r = self._router()
        r.learn(("uf",), "closed", routed=False, hit=False)
        assert r.route(("uf",)) == "closed"

    def test_none_key_never_routes(self):
        r = self._router()
        r.learn(None, "closed", routed=False, hit=False)
        assert r.route(None) is None

    def test_reroutes_to_new_winner(self):
        r = self._router()
        r.learn(("uf",), "closed", routed=False, hit=False)
        r.learn(("uf",), "closed_int", routed=True, hit=False)
        assert r.route(("uf",)) == "closed_int"

    def test_disables_when_misses_dominate(self):
        r = self._router()
        key = ("uf",)
        r.learn(key, "closed", routed=False, hit=False)
        for _ in range(_ClassRouter.DISABLE_MIN_MISSES):
            r.learn(key, None, routed=True, hit=False)
        assert r.route(key) is None

    def test_hits_keep_class_enabled(self):
        r = self._router()
        key = ("uf",)
        r.learn(key, "closed", routed=False, hit=False)
        for _ in range(6):
            r.learn(key, "closed", routed=True, hit=True)
        for _ in range(_ClassRouter.DISABLE_MIN_MISSES):
            r.learn(key, None, routed=True, hit=False)
        assert r.route(key) == "closed"
