import json
import logging
import subprocess

from . import converter
from .utils.args import ARGS
from .utils.io import load_apc_dump, load_json


def diff():
    """Format two inputs (as JSON or text) and launch an external diff viewer (`meld`)."""
    before = load_apc_dump(ARGS().input_before)
    after = load_apc_dump(ARGS().input_after)

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
            before_model = None
            after_model = None
            if ARGS().with_model:
                before_model = load_json(ARGS().with_model)
                after_model = before_model
            elif ARGS().with_before_model:
                before_model = load_json(ARGS().with_before_model)
            elif ARGS().with_after_model:
                after_model = load_json(ARGS().with_after_model)

            before_formatted = ARGS().input_before.with_name(
                f".formatted_{ARGS().input_before.name}.txt"
            )
            after_formatted = ARGS().input_after.with_name(
                f".formatted_{ARGS().input_after.name}.txt"
            )
            with open(before_formatted, "w") as f:
                converter.convert_to_text(f, before, before_model)
                f.flush()
            with open(after_formatted, "w") as f:
                converter.convert_to_text(f, after, after_model)
                f.flush()

        case _:
            logging.error(f"unknown format: {ARGS().format}")

    subprocess.run(["meld", before_formatted, after_formatted])

    before_formatted.unlink()
    after_formatted.unlink()
