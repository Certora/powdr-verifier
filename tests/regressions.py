"""Folder regressions: tests/regression_cases/<name>/case.toml + pytest."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from src.lens import resolve
from src.paths import POWDR_DIR, POWDR_DUMPS_DIR, VERIFIER_DIR, WORKSPACE_DIR
from src.simplify.rust import resolve_simplifier_bin

CASES_ROOT = VERIFIER_DIR / "tests" / "regression_cases"
_SCRIPTS = {"main.py": VERIFIER_DIR / "main.py", "orchestrate.py": VERIFIER_DIR / "orchestrate.py"}
_PH = re.compile(r"\{(\w+)\}")
_SKIP_INPUTS = {"type", "dataset", "check"}
_SOURCE_META = {"dataset", "block", "substitutions", "powdr_commit", "powdr_test", "match"}


@dataclass(frozen=True)
class Case:
    name: str
    path: Path
    tags: tuple[str, ...]
    description: str
    requires: tuple[str, ...]
    source: dict[str, Any] | None
    inputs: dict[str, str]
    steps: tuple[dict[str, Any], ...]
    asserts: tuple[dict[str, Any], ...]

    @property
    def id(self) -> str:
        return self.name


@dataclass
class Step:
    exit_code: int
    stdout: str
    stderr: str
    json_out: Any | None = None


def _load_case(manifest: Path) -> Case:
    raw = tomllib.loads(manifest.read_text())
    meta = raw.get("case", {})
    return Case(
        name=manifest.parent.name,
        path=manifest.parent,
        tags=tuple(meta.get("tags", [])),
        description=(meta.get("description") or "").strip(),
        requires=tuple(meta.get("requires", [])),
        source=raw.get("source"),
        inputs={k: str(v) for k, v in raw.get("inputs", {}).items()},
        steps=tuple(raw.get("steps", [])),
        asserts=tuple(raw.get("assert", [])),
    )


def discover_cases(root: Path | None = None) -> list[Case]:
    root = root or CASES_ROOT
    return [_load_case(p) for p in sorted(root.glob("*/case.toml"))] if root.is_dir() else []


def _powdr_head() -> str | None:
    if not POWDR_DIR.is_dir():
        return None
    try:
        r = subprocess.run(
            ["git", "-C", str(POWDR_DIR), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
        )
        return r.stdout.strip()
    except (subprocess.CalledProcessError, OSError):
        return None


def _ctx(case: Case, work: Path) -> dict[str, str]:
    ctx = {"case": str(case.path.resolve()), "work": str(work.resolve())}
    ctx.update({k: str((case.path / v).resolve()) for k, v in case.inputs.items()})
    if case.inputs.get("dataset"):
        ctx["dataset"] = case.inputs["dataset"]
    elif case.inputs.get("type") == "dumps":
        ctx["dataset"] = f"regression-{case.name}"
    return ctx


def _xp(s: str, ctx: dict[str, str]) -> str:
    return _PH.sub(lambda m: ctx[m.group(1)], s)


def _missing(case: Case) -> str | None:
    for req in case.requires:
        if req == "powdr" and not POWDR_DIR.is_dir():
            return "powdr checkout missing"
        if req == "rust-simplifier" and resolve_simplifier_bin() is None:
            return "simplifier binary not built"
    missing = [
        rel
        for k, rel in case.inputs.items()
        if k not in _SKIP_INPUTS and not (case.path / rel).is_file()
    ]
    return f"missing inputs: {', '.join(missing)}" if missing else None


def _action(data: Any) -> dict[str, Any] | None:
    return data["__Action"] if isinstance(data, dict) and "__Action" in data else None


def _walk(data: Any):
    if (a := _action(data)) is not None:
        yield a
        for c in a.get("actions", []):
            yield from _walk(c)


def _pass_action(data: Any, name: str) -> dict[str, Any] | None:
    for a in _walk(data):
        base = a.get("name", "").split("-", 1)[0]
        if a.get("name") == name or base == name:
            return a
    return None


def _jget(data: Any, path: str) -> Any:
    cur = data
    for part in path.split("."):
        cur = _action(cur) if part == "__Action" and isinstance(cur, dict) else (
            cur.get(part) if isinstance(cur, dict) else None
        )
    return cur


def _stat(value: Any, spec: dict[str, Any], label: str) -> None:
    if "equals" in spec:
        assert value == spec["equals"], f"{label}: {value!r} != {spec['equals']!r}"
    if "min" in spec:
        assert value is not None and value >= spec["min"], f"{label}: {value!r} < {spec['min']}"
    if "max" in spec:
        assert value is not None and value <= spec["max"], f"{label}: {value!r} > {spec['max']}"


def _norm(text: str) -> str:
    return "\n".join(line.rstrip() for line in text.strip().splitlines()) + "\n"


def _run_step(script: str, args: list[str], *, timeout: int, capture_json: bool) -> Step:
    cmd = ["timeout", f"{timeout}s", str(_SCRIPTS[script]), *args]
    cp = subprocess.run(cmd, cwd=WORKSPACE_DIR, capture_output=True, text=True)
    js = json.loads(cp.stdout) if capture_json and cp.returncode == 0 and cp.stdout.strip() else None
    return Step(cp.returncode, cp.stdout, cp.stderr, js)


def _asserts(case: Case, steps: list[Step], ctx: dict[str, str], *, update: bool) -> None:
    for i, spec in enumerate(case.asserts):
        k, L = spec["kind"], f"case {case.name} assert[{i}] ({spec['kind']})"
        if k == "exit_ok":
            s = steps[int(spec["step"])]
            assert s.exit_code == 0, f"{L}: exit {s.exit_code}\n{s.stderr}\n{s.stdout}"
        elif k == "check_result":
            s = steps[int(spec["step"])]
            a = _action(s.json_out)
            assert a and a.get("result") == spec["result"], f"{L}: {a and a.get('result')!r}"
        elif k in ("pass_stats", "pass_unchanged"):
            s, p = steps[int(spec["step"])], _pass_action(steps[int(spec["step"])].json_out, spec["pass"])
            assert p, f"{L}: pass {spec['pass']!r} not found"
            _stat(p.get(spec.get("field", "asserts_changed")), {"equals": 0} if k == "pass_unchanged" else spec, L)
        elif k == "isqf":
            p = _pass_action(steps[int(spec["step"])].json_out, "isqf")
            assert p and p.get("result") == spec.get("result", "qf"), f"{L}: {p and p.get('result')!r}"
        elif k == "json_path":
            v = _jget(steps[int(spec["step"])].json_out, spec["path"])
            assert v == spec["equals"], f"{L}: {spec['path']!r} = {v!r}"
        elif k == "file_equals":
            act, exp = Path(_xp(spec["actual"], ctx)), Path(_xp(spec["expected"], ctx))
            text = act.read_text()
            if update:
                exp.write_text(text)
            else:
                assert exp.is_file(), f"{L}: missing {exp}"
                a, e = text, exp.read_text()
                assert (_norm(a) == _norm(e) if spec.get("normalize", True) else a == e), f"{L}: mismatch"
        elif k == "json_file_equals":
            exp = Path(_xp(spec["expected"], ctx))
            if "actual" in spec:
                act = Path(_xp(spec["actual"], ctx))
                data = json.loads(act.read_text())
            else:
                data = steps[int(spec["step"])].json_out
            if update:
                exp.write_text(json.dumps(data, indent=2) + "\n")
            else:
                assert exp.is_file(), f"{L}: missing {exp}"
                assert data == json.loads(exp.read_text()), f"{L}: JSON mismatch"
        else:
            raise ValueError(f"{L}: unknown kind {k!r}")


def run_case(case: Case, work: Path, *, update_goldens: bool = False) -> None:
    work.mkdir(parents=True, exist_ok=True)
    ctx = _ctx(case, work)
    staging = None
    if case.inputs.get("type") == "dumps" and any(s.get("script") == "orchestrate.py" for s in case.steps):
        staging = POWDR_DUMPS_DIR / ctx["dataset"]
        if staging.exists():
            shutil.rmtree(staging)
        staging.mkdir(parents=True)
        for p in case.path.glob("*.json"):
            shutil.copy2(p, staging / p.name)
    steps: list[Step] = []
    try:
        for st in case.steps:
            steps.append(
                _run_step(
                    st["script"],
                    [_xp(a, ctx) for a in st["args"]],
                    timeout=int(st.get("timeout", 60)),
                    capture_json=bool(st.get("capture_json", False)),
                )
            )
        _asserts(case, steps, ctx, update=update_goldens)
    finally:
        if staging and staging.is_dir():
            shutil.rmtree(staging, ignore_errors=True)


def update_case_dumps(name: str, *, dry_run: bool = False) -> dict[str, str]:
    case_dir = CASES_ROOT / name
    raw = tomllib.loads((case_dir / "case.toml").read_text())
    src = raw.get("source")
    if not src:
        raise ValueError(f"{name}: no [source]")
    dump_dir = resolve.group_dir(str(src["dataset"]), POWDR_DUMPS_DIR)
    block = resolve.normalize_block(str(src["block"]))
    entries = resolve.index_block(dump_dir, block)
    roles = {k: str(v) for k, v in src.items() if k not in _SOURCE_META}
    out: dict[str, str] = {"block": block}
    for role, token in roles.items():
        path = resolve.resolve_step(entries, token).path
        dest = case_dir / path.name
        out[role] = path.name
        if dry_run:
            print(f"would copy {path} -> {dest}")
        else:
            shutil.copy2(path, dest)
    if src.get("substitutions"):
        sub = resolve.substitutions_path(dump_dir, block)
        if sub is None:
            raise resolve.ResolveError(f"no substitutions for block {block}")
        out["substitutions"] = sub.name
        dest = case_dir / sub.name
        if dry_run:
            print(f"would copy {sub} -> {dest}")
        else:
            shutil.copy2(sub, dest)
    if not dry_run:
        text = (case_dir / "case.toml").read_text()
        for role, fname in out.items():
            if role == "block":
                continue
            text = re.sub(
                rf'^({re.escape(role)}\s*=\s*)".*?"',
                rf'\1"{fname}"',
                text,
                count=1,
                flags=re.MULTILINE,
            )
        if head := _powdr_head():
            if re.search(r"^powdr_commit\s*=", text, re.MULTILINE):
                text = re.sub(r'^powdr_commit\s*=.*', f'powdr_commit = "{head}"', text, flags=re.MULTILINE)
            else:
                text = re.sub(
                    r"(\[source\]\n)",
                    rf'\1powdr_commit = "{head}"\n',
                    text,
                    count=1,
                )
        (case_dir / "case.toml").write_text(text)
    return out


def _params() -> list[pytest.ParameterSet]:
    tags = {t.strip() for t in os.environ.get("REGRESSION_TAGS", "").split(",") if t.strip()}
    return [
        pytest.param(c, id=c.id)
        for c in discover_cases()
        if not tags or tags.intersection(c.tags)
    ]


@pytest.fixture
def regression_update():
    return os.environ.get("REGRESSION_UPDATE") == "1"


@pytest.fixture
def regression_work(regression_case: Case):
    work = WORKSPACE_DIR / ".tmp-regression" / regression_case.name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    yield work
    shutil.rmtree(work, ignore_errors=True)


@pytest.mark.parametrize("regression_case", _params())
def test_regression(regression_case: Case, regression_work, regression_update: bool):
    if reason := _missing(regression_case):
        pytest.skip(reason)
    run_case(regression_case, regression_work, update_goldens=regression_update)
