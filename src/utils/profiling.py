import functools
import logging
import sys
import tabulate
import time

from .args import ARGS

PROFILE_COUNT = {}
PROFILE_TIME = {}


def simple_profile(func):
    """Print the runtime of the decorated function"""

    @functools.wraps(func)
    def wrapper_timer(*args, **kwargs):
        """Time `func` and accumulate count/total time in the global profile tables."""
        start_time = time.perf_counter_ns()
        value = func(*args, **kwargs)
        end_time = time.perf_counter_ns()
        run_time = end_time - start_time
        global PROFILE_TIME
        PROFILE_TIME[func.__qualname__] = (
            PROFILE_TIME.get(func.__qualname__, 0) + run_time
        )
        global PROFILE_COUNT
        PROFILE_COUNT[func.__qualname__] = PROFILE_COUNT.get(func.__qualname__, 0) + 1
        return value

    return wrapper_timer

class Profile:
    def __init__(self, name: str):
        self.name = name

    def __enter__(self):
        self.start_time = time.perf_counter_ns()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        took = (time.perf_counter_ns() - self.start_time) / 1000000000
        logging.warning(f"{self.name} took {took:.3f} s")


def print_profile():
    """Print the profile of the functions"""
    logger = logging.getLogger(__name__)
    if logger.getEffectiveLevel() > logging.INFO:
        return
    table = [
        [name, PROFILE_COUNT[name], PROFILE_TIME[name] / 1000000000]
        for name in sorted(PROFILE_TIME.keys())
    ]
    t = tabulate.tabulate(
        table, headers=["Function", "Count", "Time"], floatfmt=".3f", tablefmt="github"
    )
    logger.info(f"Profile for {" ".join(sys.argv)}\n{t}")
