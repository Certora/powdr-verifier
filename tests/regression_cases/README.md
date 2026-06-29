# Regression cases

Folder-based regressions live under `tests/regression_cases/<name>/`. Each case has:

- `case.toml` — tags, description, inputs, command steps, assertions
- Input and golden files at the case root (original filenames, no renaming)
- `[source]` (dump-backed cases only) — where inputs come from in `powdr-dumps/`

## Running

From `verifier/` with the venv active:

```bash
pytest tests/regressions.py
pytest tests/regressions.py -k nnf-implies
pytest tests/regressions.py --collect-only
REGRESSION_UPDATE=1 pytest tests/regressions.py -k nnf-implies
REGRESSION_TAGS=smt2 pytest tests/regressions.py
```

## Adding a case

1. Create `tests/regression_cases/<name>/case.toml` (see an existing case for templates).
2. Copy inputs from `powdr-dumps/` or `data/` without renaming, or use `tests/regression_cases/scaffold.py`.
3. For APC dumps, add `[source]` with `dataset`, `block`, `powdr_commit`, and step tokens (NNN / pass@N).
4. Run and iterate; refresh goldens with `REGRESSION_UPDATE=1`.

## Refreshing dumps after powdr updates

```bash
tests/regression_cases/update_dumps.py --dry-run <name>
tests/regression_cases/update_dumps.py <name>
```

See `.cursor/skills/update-regression-dumps/SKILL.md`.

## `case.toml` placeholders

| Placeholder | Value |
|-------------|-------|
| `{case}` | Case directory (absolute) |
| `{work}` | Per-run temp output dir |
| `{smt}`, `{base}`, `{before}`, `{after}`, … | Paths from `[inputs]` |
| `{dataset}` | Staging name under `powdr-dumps/` for `orchestrate.py` |

## Tags

Tags are conventions in `[case].tags`. Filter with `REGRESSION_TAGS=tag1,tag2` or `-k case-name`.

## Assertion kinds

| Kind | Purpose |
|------|---------|
| `exit_ok` | Step exited 0 |
| `check_result` | `check` step result is `unsat` / `sat` |
| `isqf` | `isqf` pass reports `qf` |
| `pass_stats` | Pass stat field (`asserts_changed`, …) |
| `pass_unchanged` | `asserts_changed == 0` |
| `json_path` | Drill into captured Action JSON |
| `file_equals` | Compare `{work}/…` to a case-root golden |
| `json_file_equals` | JSON deep-equality (`actual` path or captured stdout) |
