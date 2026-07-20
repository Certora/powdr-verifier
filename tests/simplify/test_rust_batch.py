from pathlib import Path
from unittest import mock

import pytest

from src.simplifier import DEFAULT_TACTIC, TACTIC_QEPREFIX, _group_tactics


def test_group_rust_tactics_batches_consecutive():
    tactics = "nnf:evaluator:r#z3-propagate-values:r#z3-solve-eqs:demod".split(":")
    groups = _group_tactics(tactics, default_executor="r")
    assert groups == [
        ("r", ["nnf", "evaluator", "r#z3-propagate-values", "r#z3-solve-eqs", "demod"]),
    ]


def test_group_explicit_python_prefix():
    tactics = "p#nnf:r#evaluator:p#demod".split(":")
    groups = _group_tactics(tactics)
    assert groups == [
        ("p", ["p#nnf"]),
        ("r", ["r#evaluator"]),
        ("p", ["p#demod"]),
    ]


def test_group_mixed_python_prefixes_batch_together():
    tactics = "nnf:p#demod:normalize".split(":")
    groups = _group_tactics(tactics, default_executor="r")
    assert groups == [
        ("r", ["nnf"]),
        ("p", ["p#demod"]),
        ("r", ["normalize"]),
    ]


def test_group_default_tactic_uses_default_executor():
    tactics = DEFAULT_TACTIC.split(":")
    groups = _group_tactics(tactics)
    assert all(executor == "p" for executor, _ in groups)
    assert not any(t.startswith(("r#", "p#")) for t in tactics)

    groups_rust = _group_tactics(tactics, default_executor="r")
    assert all(executor == "r" for executor, _ in groups_rust)


def test_group_isqf_stays_in_rust_batch():
    tactics = TACTIC_QEPREFIX.split(":")
    groups = _group_tactics(tactics, default_executor="r")
    # diff_vars is a native rust pass, so the whole QE prefix stays in one rust
    # batch (no python-only pass forces a split).
    assert groups == [
        ("r", ["nnf", "skolem", "lift", "witness", "demod", "isqf", "diff_vars"]),
    ]


def test_group_unknown_executor_skipped():
    tactics = "nnf:x#evaluator:demod".split(":")
    groups = _group_tactics(tactics, default_executor="r")
    assert groups == [("r", ["nnf", "demod"])]


def test_rust_batch_single_subprocess():
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    tactic = "r#z3-propagate-values:r#z3-solve-eqs"
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="(check-sat)\n", stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            with mock.patch("src.simplify.rust._string_to_script") as parse:
                parse.return_value = smt_script
                simplify_smt_script(smt_script, tactic=tactic, timeout=60.0)[0]
        assert run.call_count == 1
        cmd = run.call_args.args[0]
        assert "z3-propagate-values:z3-solve-eqs" in cmd
        assert "--timeout" in cmd


def test_rust_batch_forwards_timeout():
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    tactic = "r#nnf"
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="(check-sat)\n", stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            with mock.patch("src.simplify.rust._string_to_script") as parse:
                parse.return_value = smt_script
                simplify_smt_script(smt_script, tactic=tactic, timeout=30.0)[0]
        cmd = run.call_args.args[0]
        idx = cmd.index("--timeout")
        assert 0 < float(cmd[idx + 1]) <= 28


def test_rust_batch_wraps_perf_when_cprofile(tmp_path):
    from src.simplify.rust import run_rust_pipeline
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol
    from src.utils.enums import FieldTypes

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    out_path = tmp_path / "verify-001.smt2"
    profile_data = tmp_path / "rust-cprofile-verify-001.data"
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="(check-sat)\n", stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = Path("/bin/simplifier")
            with mock.patch("src.simplify.rust._string_to_script") as parse:
                parse.return_value = smt_script
                with mock.patch("src.simplify.rust.ARGS") as args:
                    args.return_value.cprofile = True
                    args.return_value.pretty = False
                    args.return_value.field_type = FieldTypes.BABYBEAR
                    with mock.patch("src.simplify.rust.shutil.which") as which:
                        which.side_effect = lambda name: "/usr/bin/perf" if name == "perf" else None
                        with mock.patch.object(Path, "is_file", return_value=True):
                            with mock.patch(
                                "src.simplify.rust.emit_perf_profile_summary"
                            ):
                                run_rust_pipeline(
                                smt_script,
                                "r#nnf",
                                timeout=30.0,
                                profile_output=out_path,
                            )
        cmd = run.call_args.args[0]
        assert cmd[0] == "/usr/bin/perf"
        assert "record" in cmd
        f_idx = cmd.index("-F")
        assert int(cmd[f_idx + 1]) == 99
        o_idx = cmd.index("-o")
        assert cmd[o_idx + 1] == str(profile_data)
        sep = cmd.index("--")
        assert cmd[sep + 1] == "/bin/simplifier"
        assert "--timeout" in cmd


def test_rust_batch_emits_per_tactic_actions():
    from src.report.action import Action
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    tactic = "r#nnf:r#evaluator"
    stderr = (
        '{"pass":"nnf","asserts":1,"asserts_changed":0,"running_time":0.12}\n'
        '{"pass":"evaluator","asserts_total":1,"asserts_changed":0,"running_time":0.34}\n'
    )
    parent = Action("simplify-programmatic")
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="(check-sat)\n", stderr=stderr)
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            with mock.patch("src.simplify.rust._string_to_script") as parse:
                parse.return_value = smt_script
                simplify_smt_script(
                    smt_script, tactic=tactic, timeout=60.0, parent_action=parent
                )[0]
    assert [a.name for a in parent.actions] == ["r#nnf", "r#evaluator"]
    assert parent.actions[0].running_time == pytest.approx(0.12)
    assert parent.actions[1].running_time == pytest.approx(0.34)
    assert parent.actions[0].enter_time is not None
    assert parent.actions[1].exit_time is not None
    assert parent.actions[0].executor == "rust"
    assert parent.actions[1].executor == "rust"


def test_rust_batch_error_fallback_labels_executor_not_fallback_string():
    from src.report.action import Action
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    parent = Action("simplify-programmatic")
    with mock.patch("src.simplifier.run_rust_pipeline", side_effect=RuntimeError("boom")):
        simplify_smt_script(
            smt_script, tactic="r#nnf", timeout=60.0, parent_action=parent
        )[0]
    assert parent.actions[0].name == "rust-fallback"
    assert parent.actions[0].fallback is True
    assert parent.actions[0].reason == "error"
    assert parent.actions[1].executor == "python"
    assert parent.actions[1].fallback is None


def test_rust_batch_fallback_dump_steps(tmp_path):
    from src.report.action import Action
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    out = tmp_path / "out.smt2"
    parent = Action("simplify-programmatic")
    with mock.patch("src.simplifier.run_rust_pipeline", side_effect=RuntimeError("boom")):
        with mock.patch("src.simplifier.ARGS") as args:
            args.return_value.dump_steps = True
            simplify_smt_script(
                smt_script,
                tactic="r#nnf",
                timeout=60.0,
                output=out,
                parent_action=parent,
            )[0]
    assert (tmp_path / "out.01.r#nnf.smt2").is_file()


def test_python_executor_labels_passes_without_fallback():
    from src.report.action import Action
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    parent = Action("simplify-programmatic")
    # Force python explicitly (the default executor is rust) to check a genuine
    # python pass is labeled "python" and not marked as a fallback.
    simplify_smt_script(smt_script, tactic="p#nnf", timeout=60.0, parent_action=parent)[0]
    assert parent.actions[0].executor == "python"
    assert parent.actions[0].fallback is None


def test_rust_batch_forwards_pretty():
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script
    from src.smt_backends.pysmt import INT, Equals, Int, Symbol

    x = Symbol("x", INT)
    smt_script = script.SmtLibScript()
    smt_script.commands = [
        script.SmtLibCommand("declare-fun", [x, INT]),
        script.SmtLibCommand("assert", [Equals(x, Int(1))]),
        script.SmtLibCommand("check-sat", []),
    ]
    tactic = "r#nnf"
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="(check-sat)\n", stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            with mock.patch("src.simplify.rust._string_to_script") as parse:
                parse.return_value = smt_script
                with mock.patch("src.simplify.rust.ARGS") as args:
                    args.return_value.pretty = True
                    simplify_smt_script(smt_script, tactic=tactic, timeout=60.0)[0]
        cmd = run.call_args.args[0]
        assert cmd[0] == "/bin/simplifier"
        assert "--pretty" in cmd
        assert "nnf" in cmd


def test_rust_first_forwards_input_file(tmp_path):
    from src.simplifier import simplify_smt_script

    smt_in = tmp_path / "in.smt2"
    smt_out = tmp_path / "out.smt2"
    smt_in.write_text("(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n")
    tactic = "r#nnf"
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="", stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            smt_script, wrote_final = simplify_smt_script(
                None,
                tactic=tactic,
                timeout=60.0,
                output=smt_out,
                input_path=smt_in,
            )
        assert run.call_count == 1
        cmd = run.call_args.args[0]
        assert str(smt_in) in cmd
        assert str(smt_out) in cmd
        assert run.call_args.kwargs.get("input") is None
        assert smt_script is None
        assert wrote_final is True


def test_rust_first_then_python_parses_intermediate(tmp_path):
    from src.simplifier import simplify_smt_script
    from src.smt.utils import script

    smt_in = tmp_path / "in.smt2"
    smt_in.write_text("(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n")
    tactic = "r#isqf:p#pretty"
    rust_out = "(check-sat)\n"
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout=rust_out, stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            # A following python group makes the rust batch write to a temp file,
            # which is read back via _bytes_to_script for the python group.
            with mock.patch("src.simplify.rust._bytes_to_script") as parse:
                parsed = script.SmtLibScript()
                parse.return_value = parsed
                smt_script, wrote_final = simplify_smt_script(
                    None,
                    tactic=tactic,
                    timeout=60.0,
                    input_path=smt_in,
                )
        cmd = run.call_args.args[0]
        assert str(smt_in) in cmd
        assert run.call_args.kwargs.get("input") is None
        parse.assert_called_once()
        assert smt_script is parsed
        assert wrote_final is False


def test_simplify_skips_python_io_for_full_rust(tmp_path):
    from src.report.action import Action
    from src.simplifier import simplify

    smt_in = tmp_path / "in.smt2"
    smt_out = tmp_path / "out.smt2"
    smt_in.write_text("(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n")
    with mock.patch("src.simplify.rust.subprocess.run") as run:
        run.return_value = mock.Mock(returncode=0, stdout="", stderr="")
        with mock.patch("src.simplify.rust.resolve_simplifier_bin") as resolve:
            resolve.return_value = mock.Mock(is_file=lambda: True, __str__=lambda s: "/bin/simplifier")
            with mock.patch("src.simplifier.ARGS") as args:
                args.return_value.input = smt_in
                args.return_value.output = smt_out
                args.return_value.tactic = "default"
                args.return_value.default_executor = "r"
                args.return_value.optimization_step = None
                args.return_value.timeout = 60.0
                action = simplify()
    names = [a.name for a in action.actions]
    assert "load" not in names
    assert "dump" not in names


def test_simplify_python_io_for_full_python(tmp_path):
    from src.simplifier import _load_script, simplify

    smt_in = tmp_path / "in.smt2"
    smt_out = tmp_path / "out.smt2"
    smt_in.write_text("(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n")
    with mock.patch("src.simplifier._load_script", wraps=_load_script) as load:
        with mock.patch("src.simplifier.write_smtlib_script") as dump:
            with mock.patch("src.simplifier.ARGS") as args:
                args.return_value.input = smt_in
                args.return_value.output = smt_out
                args.return_value.tactic = "nnf"
                args.return_value.default_executor = "p"
                args.return_value.optimization_step = None
                args.return_value.timeout = 60.0
                args.return_value.dump_steps = False
                action = simplify()
    names = [a.name for a in action.actions]
    assert "load" in names
    assert "dump" in names
    load.assert_called_once()
    dump.assert_called_once()


def test_format_perf_report_summary_extracts_meta_and_rows():
    from src.simplify.rust import _format_perf_report_summary

    stdout = (
        "# Samples: 158  of event 'cycles:P'\n"
        "#\n"
        "# Overhead       Samples  Symbol\n"
        "# ........  ............  ......\n"
        "    10.12%             6  [.] format_ns::flat(ast_manager&, app*)\n"
        "     7.99%             5  [.] recurse_expr<app*, format_ns::flat_visitor, true, true>::process(expr*)\n"
        "     5.82%             0  [k] 0x9b333d9300000006\n"
    )
    summary = _format_perf_report_summary(stdout, top_n=5)
    assert summary[0].startswith("Samples:")
    assert "10.12%  format_ns::flat(ast_manager&, app*)" in summary
    assert any("recurse_expr" in line for line in summary)
    assert not any("0x9b333d93" in line for line in summary)


def test_emit_perf_profile_summary_logs_on_success(tmp_path, caplog):
    import logging

    from src.simplify.rust import emit_perf_profile_summary

    profile = tmp_path / "rust-cprofile-test.data"
    profile.write_bytes(b"x" * 1024)
    stdout = (
        "# Samples: 10  of event 'cycles:P'\n"
        "# Overhead       Samples  Symbol\n"
        "    50.00%            10  [.] simplifier::passes::nnf::apply\n"
    )
    with mock.patch("src.simplify.rust.shutil.which", return_value="/usr/bin/perf"):
        with mock.patch("src.simplify.rust.subprocess.run") as run:
            run.return_value = mock.Mock(returncode=0, stdout=stdout, stderr="")
            with caplog.at_level(logging.WARNING):
                emit_perf_profile_summary(profile, top_n=5, timeout_sec=10.0)
    assert "perf profile summary" in caplog.text
    assert "simplifier::passes::nnf::apply" in caplog.text
    cmd = run.call_args.args[0]
    assert cmd[0] == "/usr/bin/perf"
    assert "report" in cmd
    assert "--sort=symbol" in cmd
    assert "--dsos" in cmd
    assert "simplifier" in cmd


def test_emit_rust_pass_timings(caplog):
    import logging

    from src.simplify.rust import _emit_rust_pass_timings

    with caplog.at_level(logging.WARNING):
        _emit_rust_pass_timings(
            [
                {"pass": "nnf", "running_time": 0.12},
                {"pass": "evaluator", "running_time": 0.34},
            ]
        )
    assert "rust simplifier pass timings" in caplog.text
    assert "nnf: 0.120s" in caplog.text
    assert "evaluator: 0.340s" in caplog.text
