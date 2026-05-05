import subprocess
from pathlib import Path

from .utils.args import ARGS

POWDR_DIR = Path(__file__).resolve().parents[2] / "powdr"


def run_powdr_opt() -> None:
    run_cwd = Path.cwd()

    def _resolve(path: Path | None) -> Path | None:
        if path is None:
            return None
        return path if path.is_absolute() else (run_cwd / path)

    input_dump = _resolve(ARGS().input)
    output_dump = _resolve(ARGS().output)
    base_dump = _resolve(ARGS().base_dump)
    optimizer_pass = ARGS().opt_pass

    output_dump.parent.mkdir(parents=True, exist_ok=True)

    pass_args: list[Path | str] = []
    pass_args.extend(["--optimizer-pass", optimizer_pass])

    cmd: list[Path | str] = [
        "cargo",
        "run",
        "-p",
        "utils",
        "--bin",
        "optimize-dump",
        "-r",
        "--",
        "--input-dump",
        input_dump,
        "--output-dump",
        output_dump,
        *([] if base_dump is None else ["--base-dump", base_dump]),
        *pass_args,
    ]
    subprocess.run([str(c) for c in cmd], cwd=POWDR_DIR, check=True)
