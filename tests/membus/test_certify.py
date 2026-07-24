"""SMT certificates: emission shape, and (when z3 is available) unsat checks."""
import pytest

from src.membus import certify
from src.membus.rules import Analysis


def _m(c, col):
    return [c, "*", col]


def _add(*terms):
    e = terms[0]
    for t in terms[1:]:
        e = [e, "+", t]
    return e


FS0 = "from_state__timestamp_0@1"
FS1 = "from_state__timestamp_1@2"
PV = "aux__base__prev_timestamp_0@7"
LIMB = "aux__lower_decomp__0_0@8"


def _dump():
    # final-APC shape: every interaction gated by the activation selector
    iv = "is_valid@99"
    arg = [_add(_m(15360, PV), _m(15360, LIMB), 15360), "-", _m(15360, FS1)]
    return {
        "bus_interactions": [
            {"id": 1, "mult": iv, "args": [1, 8, "d0@11", 0, 0, 0, FS0]},
            {"id": 1, "mult": ["-", iv], "args": [1, 8, "d0@11", 0, 0, 0, PV]},
            {"id": 1, "mult": [iv, "*", 1], "args": [1, 12, 0, 0, 0, 0, FS1]},
            {"id": 3, "mult": 1, "args": [arg, 12]},       # bus-form R2
            {"id": 3, "mult": 1, "args": [LIMB, 17]},
        ],
        "constraints": [
            _add(FS1, _m(-1, FS0), -3),                    # Gap
            _add(FS0, _m(-1, PV), -1),                     # constraint-form R2
        ],
    }


def _negated_claim(smt2):
    return next(ln for ln in reversed(smt2.splitlines())
                if ln.startswith("(assert (not"))


def _expected_cols(an, f):
    """The columns the fact's claim must be about."""
    from src.membus.linform import names
    t = type(f).__name__
    if t == "Bound":
        return {f.col}
    if t == "Gap":
        return {f.later, f.earlier}
    if t == "RecvUpper":
        return {f.pv, f.fs}
    if t == "AffineDef":
        return {f.col, *(o for o, _ in f.weights)}
    if t == "EffKind":
        return set(names(an._orig_mult[f.ordinal]))
    if t == "Pin":
        return {f.col}
    if t == "LinZero":
        return {c for c, _ in f.coeffs}
    if t == "ExprEval":
        return set(names(f.expr))
    return set()


def test_all_facts_covered_and_certificates_emit():
    an = Analysis(_dump())
    facts = certify.all_facts(an)
    types = {type(f).__name__ for f in facts}
    assert {"Bound", "Gap", "RecvUpper", "EffKind"} <= types
    for f in facts:
        smt = certify.certificate(an, f).smt2
        assert "(check-sat)" in smt
        neg = _negated_claim(smt)
        # the negated claim must be a NON-TRIVIAL assertion ABOUT this fact: a
        # constant claim, or one mentioning none of the fact's own columns, is a
        # vacuous / mis-targeted encoding the substring check used to miss.
        assert neg not in ("(assert (not true))", "(assert (not false))")
        cols = _expected_cols(an, f)
        assert cols and any(certify._smt_sym(c) in neg for c in cols), \
            f"{type(f).__name__} negated claim omits its columns: {neg}"


def test_certificate_names_assumptions():
    from src.membus.facts import TS_MAX
    an = Analysis(_dump())
    facts = certify.all_facts(an)
    # TS_BOUND: the Gap rests on a ts Bound granted its [0, TS_MAX) domain. The
    # grant must be an actual asserted CLAIM (not merely a named-assumption
    # comment), and at exactly TS_MAX — a wrong domain is left ungranted.
    gap = next(f for f in facts if type(f).__name__ == "Gap")
    gap_grants = [ln for ln in certify.certificate(an, gap).smt2.splitlines()
                  if ln.startswith("(assert") and f" {TS_MAX})" in ln]
    assert gap_grants, "TS_BOUND domain not granted as an asserted claim"
    # ACTIVE_SELECTOR: fixes the gating column to 1 — assert the grant line.
    sel = an.active_selector
    assert sel is not None
    grant = f"(assert (= {certify._smt_sym(sel)} 1))"
    kinds = [f for f in facts if type(f).__name__ == "EffKind" and f.assumptions]
    assert kinds and any(grant in certify.certificate(an, f).smt2 for f in kinds), \
        "ACTIVE_SELECTOR grant (= sel 1) not asserted"


@pytest.mark.skipif(certify.find_z3() is None, reason="no z3 on PATH")
def test_certificates_are_unsat():
    res = certify.certify_dump(_dump(), run=True)
    assert res and all(r["result"] == "unsat" for r in res), \
        [r for r in res if r["result"] != "unsat"]


@pytest.mark.skipif(certify.find_z3() is None, reason="no z3 on PATH")
def test_bogus_fact_certificate_is_sat():
    # sanity: the harness can fail — a fabricated wrong fact must come back sat
    from src.membus.facts import Gap, Src
    an = Analysis(_dump())
    wrong = Gap(FS1, FS0, 4, sources=(Src("constraint", 0),))   # real gap is 3
    cert = certify.certificate(an, wrong)
    assert certify.run_z3(cert.smt2, certify.find_z3()) == "sat"


@pytest.mark.skipif(certify.find_z3() is None, reason="no z3 on PATH")
def test_ternary_flag_refutation_grant_is_sound():
    # The is_load refutation must grant each flag its proven [0,n) domain, not a
    # hard-coded {0,1}. A fabricated is_load=1 pin, forced only when the ternary
    # flag is treated as boolean, must come back sat: over the real domain, f=2
    # gives is_load=0. (Old bug: the boolean grant deleted the f=2 case, so this
    # certified unsat.)
    from src.membus.facts import Pin, Src
    from src.lens.normalize import BABYBEAR_PRIME as P
    inv2 = pow(2, -1, P)
    f, il = "flags__0_0@11", "is_load_0@10"
    mux = [il, "-", [1, "+", [[(-inv2) % P, "*", [f, "*", f]],
                              "+", [inv2 % P, "*", f]]]]
    ternary = [f, "*", [[f, "-", 1], "*", [f, "-", 2]]]
    an = Analysis({"constraints": [mux, ternary], "bus_interactions": []})
    wrong = Pin(il, 1, sources=(Src("constraint", 0), Src("constraint", 1)),
                refute_flags=(f,))
    cert = certify.certificate(an, wrong)
    assert f"< {certify._smt_sym(f)} 3" in cert.smt2   # proven domain, not <= 1
    assert certify.run_z3(cert.smt2, certify.find_z3()) == "sat"


def test_propagation_facts_in_all_facts():
    cons = [["g@1", "*", ["g@1", "+", -1]], ["g@1", "+", -1]]
    an = Analysis({"constraints": cons,
                   "bus_interactions": [{"id": 1, "mult": "g@1",
                                         "args": [1, 8, 0, 0, 0, 0, "t@2"]}]},
                  assume_is_valid=False)
    types = {type(f).__name__ for f in certify.all_facts(an)}
    assert {"Pin", "EffKind"} <= types
    for f in certify.all_facts(an):
        cert = certify.certificate(an, f)
        assert "(check-sat)" in cert.smt2
    with pytest.raises(ValueError, match="z3 binary not found"):
        certify.certify_dump(_dump(), run=True, z3_path="/nonexistent/z3")


@pytest.mark.skipif(certify.find_z3() is None, reason="no z3 on PATH")
def test_z3_path_explicit_binary():
    import shutil
    res = certify.certify_dump(_dump(), run=True, z3_path=shutil.which("z3"))
    assert res and all(r["result"] == "unsat" for r in res)
