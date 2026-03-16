from pathlib import Path
import subprocess
import sys


TACTICS = [
    "rewrite",
    "z3",
    "intervals",
    #"z3",
    #"z3-propagate-values",
    #"z3-solve-eqs",
    #"z3-propagate-ineqs",
    #"intervals",
    #"rewrite",
    #"z3-ctx-simplify",
    #"z3-propagate-values",
    #"z3-solve-eqs",
    #"z3-propagate-ineqs",
#    "rewrite",
#    "z3-simplify",
#    "z3-propagate-values",
#    "z3-solve-eqs",
#    "z3-propagate-ineqs",
]
SKIP = 2
SKIP_DIFF = 0


def main() -> None:
    verifier_dir = Path(__file__).resolve().parent
    current = Path("pptest-00.smt2")

    if not current.exists():
        raise FileNotFoundError(f"missing input file: {current}")

    for i, tactic in enumerate(TACTICS, start=1):
        previous = current
        current = Path(f"pptest-{i:02d}.smt2")

        if i > SKIP:
            print(f"simplifying {previous} with {tactic} -> {current}")
            subprocess.run(
                [
                    sys.executable,
                    str(verifier_dir / "main.py"),
                    "simplify",
                    str(previous),
                    tactic,
                    str(current),
                ],
                check=True,
            )

            if i > SKIP_DIFF:
                subprocess.run(["meld", str(previous), str(current)], check=True)


if __name__ == "__main__":
    main()
