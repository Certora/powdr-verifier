from .domain import INF, IntDomain, IntInterval
from .reasoner import IntervalReasoner
from .script import simplify_intervals

# Backward-compatible names used by existing simplify tests/callers.
Interval = IntInterval

__all__ = [
    "INF",
    "IntInterval",
    "IntDomain",
    "IntervalReasoner",
    "Interval",
    "simplify_intervals",
]
