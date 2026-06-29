"""cProfile helpers for the verifier CLI."""
import logging
import pstats
import sys
from pathlib import Path

_VERIFIER_ROOT = Path(__file__).resolve().parents[2]
_EXCLUDED_VERIFIER_PARTS = frozenset({".venv", "venv"})


def _is_verifier_source(filename: str) -> bool:
    if not filename or filename[0] != "/":
        return False
    try:
        rel = Path(filename).resolve().relative_to(_VERIFIER_ROOT)
    except (OSError, ValueError):
        return False
    return rel.parts[0] not in _EXCLUDED_VERIFIER_PARTS


def _verifier_source_stats(path: str, stream) -> pstats.Stats:
    stats = pstats.Stats(path, stream=stream)
    stats.stats = {
        func: data
        for func, data in stats.stats.items()
        if _is_verifier_source(func[0])
    }
    stats.all_callees = {}
    stats.fcn_list = []
    return stats


def dump_cprofile(profiler, path: str = "cprofile.prof", print_stats: int = 40) -> None:
    """Write cProfile stats to ``path`` and print a summary to stderr."""
    profiler.disable()
    profiler.dump_stats(path)
    logging.warning("cProfile written to %s", path)
    if print_stats > 0:
        stats = _verifier_source_stats(path, stream=sys.stderr)
        stats.sort_stats("cumtime")
        logging.warning(
            "cProfile summary (verifier code only, top %d by cumtime):",
            print_stats,
        )
        stats.print_stats(print_stats)
