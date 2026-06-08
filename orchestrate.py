#!/usr/bin/env python3

import argparse
from collections import defaultdict
import functools
import json
import logging
import re
import shutil
import subprocess
import sys
from io import StringIO
from pathlib import Path
from typing import Any, Optional

from src.utils.io import load_json
from src.utils.enums import XOrEncoding
from src.utils.utils import s2range
from src.utils.profiling import Profile
from src.report.action import Action
from src.report.dumpers import ActionDumper, set_report_dir
from src.paths import (
    POWDR_DIR,
    POWDR_DUMPS_DIR,
    REPORTS_DIR,
    VERIFIER_DIR,
    data_path_for_dump,
    ensure_layout,
)

ensure_layout()
set_report_dir(REPORTS_DIR)
assert POWDR_DIR.exists()

TIMEOUT_ENCODING_SEC = 60.0
TIMEOUT_SIMPLIFY_SEC = 120.0
TIMEOUT_CHECK_SEC = 60.0
TIMEOUT_DEFAULT_SEC = 60.0

_ARGS = None
PYTHON = sys.executable

def load_files_by_block(args):
    files = defaultdict(dict)
    __FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")
    for file in (POWDR_DUMPS_DIR / args.test).glob("apc_candidate_*.json"):
        if ".powdr-opt-" in file.stem:
            continue
        if m := __FILENAMERE.match(file.name):
            block = int(m.group(1))
            if args.blocks is None or block in args.blocks:
                step = int(m.group(2))
                assert step not in files[block]
                files[block][step] = file
                if "eliminations" not in files[block]:
                    tmp = POWDR_DUMPS_DIR / args.test / f"apc_candidate_{block}_substitutions.json"
                    if tmp.exists():
                        files[block]["eliminations"] = tmp
    
    return files

def parallelize(func):
    def wrapped(*args, **kwargs):
        if _ARGS.jobs == 1:
            for t in args:
                func(*t, **kwargs)
        else:
            import concurrent.futures
            with concurrent.futures.ThreadPoolExecutor(max_workers=_ARGS.jobs) as executor:
                for t in args:
                    executor.submit(func, *t, **kwargs)
    return wrapped

__FILENAMERE = re.compile("apc_candidate_(\\d+)_(\\d+)(.*)\\.json")
def parse_range(files: dict, steps):
    for id in sorted([k for k in files.keys() if isinstance(k, int)]):
        if id in steps:
            yield files[id]


def parse_paired_range(files: dict, steps):
    ids = sorted([i for i in files.keys() if isinstance(i, int)])
    if steps is None:
        yield (files[ids[0]], files[ids[-1]])
        return

    for k in range(max(steps.start, min(*ids)), min(steps.stop, max(*ids))):
        if k in files and k+1 in files:
            yield (files[k], files[k+1])


def __split_args_for_main(args):
    from src.utils.args import __build_parser
    _, leftover = __build_parser(skip_subparsers=True).parse_known_args(args)
    return [a for a in args if a not in leftover], leftover


def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument('command', choices=[
        'powdr',
        'powdr-guest',
        'verify-opt',
        'trace',
        'diff',
        'evaluate',
        'eval',
        'verify',
    ])
    parser.add_argument('test', type=str)
    parser.add_argument('k', type=str, nargs='*')
    parser.add_argument('--clean', action='store_true')
    parser.add_argument("--with-patch", type=Path, default=None)
    parser.add_argument("-j", "--jobs", type=int, default=1)

    global _ARGS
    _ARGS, leftover = parser.parse_known_args()
    _ARGS._main_args, _ARGS._sub_args = __split_args_for_main(leftover)
    _ARGS._additional_args = []


    _ARGS.blocks = None
    _ARGS.steps = None
    match _ARGS.k:
        case []:
            pass
        case [steps]:
            pass
            _ARGS.steps = s2range(steps)
        case [blocks, steps]:
            _ARGS.blocks = s2range(blocks)
            _ARGS.steps = s2range(steps)
        case _:
            raise ValueError(f"invalid k: {_ARGS.k}")

    return _ARGS


def __run_main(
    command,
    *args,
    parse_output: bool = False,
    extra_args=None,
    timeout: float = TIMEOUT_DEFAULT_SEC,
) -> Optional[Any]:
    """Run ``main.py`` as a subprocess. With ``parse_output=True``, capture stdout and return ``load_json`` of it."""
    extra = list(extra_args or [])
    cmd = [PYTHON, VERIFIER_DIR / "main.py", *_ARGS._additional_args, *_ARGS._main_args, command, *args, *extra, *_ARGS._sub_args]
    cmdstr = " ".join(map(str, cmd))
    if parse_output:
        try:
            result = subprocess.run(
                cmd,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
                timeout=timeout,
            )
            return load_json(StringIO(result.stdout))
        except subprocess.TimeoutExpired:
            logging.error(f"timed out running {cmdstr}")
            return Action(command, result="timeout")
        except json.JSONDecodeError:
            logging.error(f"failed to parse output of {cmdstr}:\n{result.stdout}")
            return Action(command, result="invalid-json")
    try:
        subprocess.run(cmd, check=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        logging.error(f"timed out running {cmdstr}")
    return None

_DEFAULT_TACTIC = (
    "nnf:evaluator:skolem:lift:witness:flatten_outer_array:z3-propagate-values:isqf:bounds:rewrite:gxor:mod_inv:demod:domain_probe:z3-propagate-values:pretty"
)


def __do_simplify(input, output, tactic=None):
    if tactic is None:
        tactic = _DEFAULT_TACTIC
    logging.info(f"simplifying with {tactic} {input.relative_to(Path.cwd())}")
    return __run_main(
        "simplify",
        input,
        tactic,
        output,
        parse_output=True,
        extra_args=["--timeout", str(TIMEOUT_SIMPLIFY_SEC - 5)],
        timeout=TIMEOUT_SIMPLIFY_SEC,
    )

def with_patch(func):
    @functools.wraps(func)
    def wrapped(*args, **kwargs):
        patch = None
        if _ARGS.with_patch is not None:
            patch = _ARGS.with_patch.resolve()
        
        try:
            if patch is not None:
                logging.info(f"applying {patch}")
                subprocess.run(["git", "apply", patch], cwd=POWDR_DIR, check=True)
        
            return func(*args, **kwargs, dirsuffix = f"-{patch.stem}" if patch is not None else "")
        finally:
            if patch is not None:
                logging.info(f"undoing {patch}")
                subprocess.run(["git", "apply", "-R", patch], cwd=POWDR_DIR, check=True)

    return wrapped

@with_patch
def run_powdr(test, dirsuffix = ""):
    dir = POWDR_DUMPS_DIR.relative_to(POWDR_DIR / "openvm", walk_up=True) / f"{test}{dirsuffix}"
    cmd = [
        f"APC_EXPORT_PATH={dir}",
        "APC_EXPORT_LEVEL=3",
        f"cargo test {test} -- --no-capture --exact",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(" ".join(cmd), shell=True, cwd=POWDR_DIR, check=True)

@with_patch
def run_powdr_guest(test, dirsuffix = ""):
    dir = POWDR_DUMPS_DIR.relative_to(POWDR_DIR, walk_up=True) / f"{test}{dirsuffix}"
    cmd = [
        f"APC_EXPORT_PATH={dir}",
        "APC_EXPORT_LEVEL=3",
        f"cargo run -p cli-openvm-riscv --bin powdr_openvm_riscv -r -- compile {test} --input 1 --autoprecompiles 1 --apc-candidates-dir {dir}",
    ]
    logging.warning(f"running {' '.join(cmd)}")
    subprocess.run(" ".join(cmd), shell=True, cwd=POWDR_DIR, check=True)

def run_trace(*files):
    for f in files:
        logging.warning(f"running tracer on {f.relative_to(Path.cwd())}")
        with ActionDumper("trace", _ARGS.test, f) as dump:
            trace_smt2 = data_path_for_dump(f, f"trace-{f.stem}.smt2")
            res_trace = __run_main("trace", f, trace_smt2, parse_output=True)
            dump += res_trace
            for file in sorted(res_trace.outputs):
                with dump.action("check") as check:
                    check += { "inputs": [file] }
                    res_simp = __do_simplify(file, file.with_suffix(".rewrite.smt2"))
                    check += res_simp
                    for rewritten in res_simp.outputs:
                        check += __run_main(
                            "check",
                            rewritten,
                            "--dump-model",
                            rewritten.with_suffix(".model"),
                            parse_output=True,
                            timeout=TIMEOUT_CHECK_SEC,
                        )

def run_diff(*pairs):
    for a,b in pairs:
        logging.warning(f"diffing {a.relative_to(Path.cwd())} and {b.relative_to(Path.cwd())}")
        __run_main("diff", a, b)

def run_evaluate(first, *files):
    for f in files:
        model = data_path_for_dump(f, f"trace-{f.stem}.model")
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        subprocess.run([
            PYTHON, VERIFIER_DIR / "evaluate.py",
            "--base-dump", first,
            f,
            model,
        ], check=True)

def run_eval(*files):
    for f in files:
        model = data_path_for_dump(f, f"trace-{f.stem}.model")
        if not model.exists():
            logging.warning(f"can not eval {f} because there is no model")
            continue
        logging.warning(f"evaluating trace from {model.relative_to(Path.cwd())} on {f.relative_to(Path.cwd())}")
        __run_main("eval", f, model)

def _parse_step_and_pass(file: Path) -> tuple[int, str]:
    m = __FILENAMERE.match(file.name)
    assert m is not None, file
    step = int(m.group(2))
    passname = m.group(3).removeprefix("_")
    return step, passname

def run_verify_opt(files: dict, pairs):
    for input_file, next_file in pairs:
        _, next_pass = _parse_step_and_pass(next_file)
        if not next_pass:
            logging.warning(f"could not infer next pass from {next_file.name}, skipping")
            continue

        output = input_file.with_name(f"{input_file.stem}.powdr-opt-{next_pass}.json")
        logging.warning(
            f"running powdr-opt {next_pass} on {input_file.relative_to(Path.cwd())}"
        )
        powdr_opt_args = [input_file, next_pass, output]
        if 0 in files:
            powdr_opt_args += ["--base-dump", files[0]]
        __run_main("powdr-opt", *powdr_opt_args)
        run_verify((input_file, output))

@parallelize
def run_verify(a, b):
    with ActionDumper("verify", _ARGS.test, a, b) as a_verify:
        logging.warning(f"verify equivalence of {a.relative_to(Path.cwd())} and {b.relative_to(Path.cwd())}")
        first = data_path_for_dump(a, f"verify-{a.stem}-{b.stem}.smt2")
        res_verify = __run_main("verify", a, b, first, parse_output=True, timeout=TIMEOUT_ENCODING_SEC)
        res_verify.name = "verify-encode"
        a_verify += res_verify
        for file in sorted(res_verify.outputs or []):
            with a_verify.action("check", inputs=[file]) as a_check:
                res_simp = __do_simplify(file, file.with_suffix(".rewrite.smt2"))
                a_check += res_simp
                for rewritten in (res_simp.outputs or []):
                    a_check += __run_main(
                        "check",
                        rewritten,
                        "--dump-model", file.with_suffix(".model"),
                        parse_output=True,
                        timeout=TIMEOUT_CHECK_SEC,
                    )

if __name__ == '__main__':
    args = parse_args()

    match args.command:
        case 'powdr':
            if args.clean:
                shutil.rmtree(POWDR_DUMPS_DIR / args.test, ignore_errors=True)
            run_powdr(args.test)
            exit(0)
        case 'powdr-guest':
            if args.clean:
                shutil.rmtree(POWDR_DUMPS_DIR / args.test, ignore_errors=True)
            run_powdr_guest(args.test)
            exit(0)
    
    all_files = load_files_by_block(args)

    if not all_files:
        logging.warning(f"no files found for {args.test}, did you run powdr?")

    try:
        for i,(block,files) in enumerate(sorted(all_files.items())):
            logging.warning(f"processing block {i+1} of {len(all_files)}")
            args._additional_args = []
            if 0 in files:
                args._additional_args += ["--base-dump", files[0]]
            if "eliminations" in files:
                args._additional_args += ["--eliminations", files["eliminations"]]

            match args.command:
                case 'trace':
                    run_trace(*parse_range(files, args.steps))
                case 'diff':
                    run_diff(*parse_paired_range(files, args.steps))
                case 'evaluate':
                    run_evaluate(files[0], *parse_range(files, args.steps))
                case 'eval':
                    run_eval(*parse_range(files, args.steps))
                case 'verify':
                    run_verify(*parse_paired_range(files, args.steps))
                case 'verify-opt':
                    run_verify_opt(files, parse_paired_range(files, args.steps))

                case _:
                    logging.error(f"unknown command: {args.command}")
                    exit(1)

    except subprocess.CalledProcessError:
        pass
    except KeyboardInterrupt:
        pass
