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


def test_all_facts_covered_and_certificates_emit():
    an = Analysis(_dump())
    facts = certify.all_facts(an)
    types = {type(f).__name__ for f in facts}
    assert {"Bound", "Gap", "RecvUpper", "EffKind"} <= types
    for f in facts:
        cert = certify.certificate(an, f)
        assert "(check-sat)" in cert.smt2
        assert "(assert (not" in cert.smt2                 # the negated claim


def test_certificate_names_assumptions():
    an = Analysis(_dump())
    facts = certify.all_facts(an)
    gap = next(f for f in facts if type(f).__name__ == "Gap")
    cert = certify.certificate(an, gap)
    assert "TS_BOUND" in cert.smt2
    kinds = [f for f in facts if type(f).__name__ == "EffKind"]
    iv = [f for f in kinds if f.assumptions]
    assert iv and any("ACTIVE_SELECTOR" in certify.certificate(an, f).smt2 for f in iv)


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


def test_z3_path_override():
    with pytest.raises(ValueError, match="z3 binary not found"):
        certify.certify_dump(_dump(), run=True, z3_path="/nonexistent/z3")


@pytest.mark.skipif(certify.find_z3() is None, reason="no z3 on PATH")
def test_z3_path_explicit_binary():
    import shutil
    res = certify.certify_dump(_dump(), run=True, z3_path=shutil.which("z3"))
    assert res and all(r["result"] == "unsat" for r in res)
