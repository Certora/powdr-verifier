"""``Action`` subclasses that persist JSON summaries under a configurable report root."""
import os
from pathlib import Path

from .action import Action
from ..utils.io import dump_json
from ..utils.process import is_memout_text

BASE_REPORT_DIR = None
def set_report_dir(report_dir: Path):
    global BASE_REPORT_DIR
    BASE_REPORT_DIR = report_dir

class ActionDumper(Action):
    def __init__(self, name: str, test: str, *input: Path):
        super().__init__(
            name,
            test=test,
            inputs=input
        )
        self.test = test
        self.input = input

    def dump_to(self, target: Path):
        os.makedirs(target.parent, exist_ok=True)
        with open(target, "w") as f:
            dump_json(self, f, indent=4)

    def __exit__(self, exc_type, exc_value, traceback):
        super().__exit__(exc_type, exc_value, traceback)
        if exc_type is not None and not issubclass(
            exc_type, (KeyboardInterrupt, SystemExit)
        ):
            msg = str(exc_value)
            self += {
                "result": "memout" if is_memout_text(msg) else "error",
                "error_message": msg,
            }
        inputs = [i.stem for i in self.inputs]
        self.dump_to(BASE_REPORT_DIR / self.test / f"{self.name}-{"-".join(inputs)}.json")
