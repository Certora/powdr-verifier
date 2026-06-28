"""JSON/APC loading, stdin/stdout path handling, and structured dumps for reports."""
import logging
import json
from pathlib import Path
import sys
from typing import Any, Optional, TextIO, Union

from ..paths import dump_input_relpath
from ..report.action import Action
from .args import ARGS

logger = logging.getLogger(__name__)


def open_file(file: Optional[Path], mode: str = "r") -> TextIO:
    if file is None or str(file) == "-":
        if mode == "r":
            return sys.stdin
        elif mode == "w":
            return sys.stdout
        else:
            raise ValueError(f"invalid mode {mode} for -")
    else:
        return open(file, mode)


def load_json(file: Union[Path, TextIO]) -> Any:
    """Load JSON from a filesystem path or a text stream."""

    def object_decoder(d: dict[Any, Any]) -> Any:
        match d:
            case {"__Path": str(path), **rest} if rest == {}:
                return Path(path)
            case {"__Action": dict(action), **rest} if rest == {}:
                return Action(**action)
            case _:
                return d

    if isinstance(file, Path):
        with open(file, "r") as f:
            return json.load(f, object_hook=object_decoder)
    return json.load(file, object_hook=object_decoder)


def dump_json(
    obj: Any,
    fp: Optional[TextIO] = sys.stdout,
    **kwargs
) -> None:
    """Like json.dump, but fp defaults to sys.stdout and pathlib.Path values are written as strings."""
    default = kwargs.pop("default", None)
    def _default(o: Any) -> Any:
        if isinstance(o, Path):
            return {"__Path": str(dump_input_relpath(o))}
        if isinstance(o, Action):
            return {"__Action": o.as_dict()}
        if default:
            return default(o)
        raise TypeError(f"Object of type {type(o).__name__} is not JSON serializable")
    json.dump(obj, fp, default=_default)


def load_apc_dump(file: Path) -> Any:
    """
    Load an apc dump and return the data.
    If the json is just the machine and not the whole apc dump,
    take the apc from the base dump and only update the machine.
    """
    data = load_json(file)
    if "block" not in data:
        if ARGS().base_dump is not None:
            base_data = load_json(ARGS().base_dump)
            assert "block" in base_data, "no block found in base dump"
            data = base_data | {"machine": data}
            logger.debug(f"took block from {ARGS().base_dump}")
        else:
            logger.error("no block found and no base dump provided")
    return data
