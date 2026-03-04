import json
import logging
import subprocess

from . import converter
from .utils.args import ARGS
from .utils.io import load_apc_dump, load_json


def diff():
    """Format two inputs (as JSON or text) and launch an external diff viewer (`meld`)."""
    before = load_apc_dump(ARGS().input_before, "before")
    after = load_apc_dump(ARGS().input_after, "after")

    match ARGS().format:
        case "json":
            before_formatted = ARGS().input_before.with_name(
                f".formatted_{ARGS().input_before.name}"
            )
            after_formatted = ARGS().input_after.with_name(
                f".formatted_{ARGS().input_after.name}"
            )
            with open(before_formatted, "w") as f:
                json.dump(before, f, indent=4)
            with open(after_formatted, "w") as f:
                json.dump(after, f, indent=4)

        case "text":
            if ARGS().with_model:
                model = load_json(ARGS().with_model, "model")
            else:
                model = None
            before_formatted = ARGS().input_before.with_name(
                f".formatted_{ARGS().input_before.name}.txt"
            )
            after_formatted = ARGS().input_after.with_name(
                f".formatted_{ARGS().input_after.name}.txt"
            )
            with open(before_formatted, "w") as f:
                converter.convert_to_text(f, before, model)
                f.flush()
            with open(after_formatted, "w") as f:
                converter.convert_to_text(f, after, model)
                f.flush()

        case _:
            logging.error(f"unknown format: {ARGS().format}")

    subprocess.run(["meld", before_formatted, after_formatted])

    before_formatted.unlink()
    after_formatted.unlink()
