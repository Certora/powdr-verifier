import functools
import tabulate
import time

from .args import ARGS

PROFILE_COUNT = {}
PROFILE_TIME = {}

def simple_profile(func):
    """Print the runtime of the decorated function"""
    @functools.wraps(func)
    def wrapper_timer(*args, **kwargs):
        start_time = time.perf_counter_ns()
        value = func(*args, **kwargs)
        end_time = time.perf_counter_ns()
        run_time = end_time - start_time
        global PROFILE_TIME
        PROFILE_TIME[func.__qualname__] = PROFILE_TIME.get(func.__qualname__, 0) + run_time
        global PROFILE_COUNT
        PROFILE_COUNT[func.__qualname__] = PROFILE_COUNT.get(func.__qualname__, 0) + 1
        return value
    return wrapper_timer

def print_profile():
    """Print the profile of the functions"""
    if not ARGS().log_profile:
        return
    table = [
        [name, PROFILE_COUNT[name], PROFILE_TIME[name] / 1000000000]
        for name in sorted(PROFILE_TIME.keys())
    ]
    t = tabulate.tabulate(
        table,
        headers=["Function", "Count", "Time"],
        floatfmt=".3f",
        tablefmt="github"
    )
    print(t)
