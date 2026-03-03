import logging
import json
from pathlib import Path
import sys
from typing import Any, Optional, TextIO

from .args import ARGS

logger = logging.getLogger(__name__)


def open_file(file: Optional[Path], mode: str = "r", newsuffix: Optional[str] = None) -> TextIO:
    if file is None or str(file) == "-":
        if mode == "r":
            return sys.stdin
        elif mode == "w":
            return sys.stdout
        else:
            raise ValueError(f"invalid mode {mode} for -")
    else:
        if newsuffix is not None:
            file = file.with_suffix(newsuffix)
        return open(file, mode)


def load_json(file: Path, label: str) -> Any:
    """Load a json file and return the data. Use label for logging."""
    with open(file, "r") as f:
        data = json.load(f)
    logger.debug(f"{label}:\n{json.dumps(data, indent=2)}")
    return data


def load_apc_dump(file: Path, label: str) -> Any:
    """
    Load an apc dump and return the data. Use label for logging.
    If the json is just the machine and not the whole apc dump,
    take the apc from the base dump and only update the machine.
    """
    data = load_json(file, label)
    if "block" not in data:
        if ARGS().base_dump is not None:
            base_data = load_json(ARGS().base_dump, "base_dump")
            assert "block" in base_data, "no block found in base dump"
            data = base_data | {"machine": data}
            logger.debug(f"took block from {ARGS().base_dump}")
        else:
            logger.error("no block found and no base dump provided")
    return data
