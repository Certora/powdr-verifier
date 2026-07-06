"""Hierarchical run record: timing, nested sub-actions, and JSON-serializable properties."""
import json
import os
from pathlib import Path
import time

_UNKNOWN_PREFIX = "unknown-"


def unknown_reason_from_result(result: str | None) -> str | None:
    if result is None:
        return None
    if result == "unknown":
        return ""
    if result.startswith(_UNKNOWN_PREFIX):
        return result[len(_UNKNOWN_PREFIX) :]
    return None


def is_timeout_reason(reason: str | None) -> bool:
    if reason is None:
        return False
    r = reason.lower()
    return (
        "timeout" in r
        or "time out" in r
        or "resource limit" in r
        or "resource limits" in r
    )


def classify_expected_vs_result(*, name: str, expected: str | None, result: str | None) -> str:
    if name == "isqf" or expected is None or result is None:
        return result if result is not None else "error"
    if result == "timeout":
        return "timeout"
    if result == "memout":
        return "memout"
    if result in ("invalid-json",) or (isinstance(result, str) and result.startswith("error")):
        return "error"
    if result in ("sat", "unsat"):
        return "success" if result == expected else "wrong"
    reason = unknown_reason_from_result(result)
    if reason is not None:
        return "timeout" if is_timeout_reason(reason) else "error"
    return "error"


class Action:
    """Context manager accumulating properties, child ``Action`` nodes, and wall times."""

    def __init__(self, name: str, **kwargs):
        self.enter_time = kwargs.pop("enter_time", None)
        self.exit_time = kwargs.pop("exit_time", None)
        self.running_time = kwargs.pop("running_time", None)
        self.actions = kwargs.pop("actions", [])
        self.properties = kwargs | { "name": name }

    def __enter__(self):
        """Start high-resolution timer."""
        self.enter_time = time.perf_counter_ns()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """Stop timer and store elapsed seconds in ``running_time``."""
        self.exit_time = time.perf_counter_ns()
        self.running_time = (self.exit_time - self.enter_time) / 1000000000
    
    def action(self, name: str, **kwargs):
        """Create a child ``Action``, append it to ``actions``, and return it for nesting."""
        action = Action(name, **kwargs)
        self.actions.append(action)
        return action

    def __iadd__(self, kwargs):
        """Merge a dict into ``properties``, append a child ``Action``, or append to a list property."""
        if isinstance(kwargs, Action):
            self.actions.append(kwargs)
        elif isinstance(kwargs, dict):
            self.properties.update(kwargs)
        elif isinstance(kwargs, tuple):
            assert len(kwargs) == 2
            assert kwargs[0] in self.properties
            self.properties[kwargs[0]].append(kwargs[1])
        else:
            raise ValueError(f"Invalid argument type: {type(kwargs)}")

        return self
    
    def __getattr__(self, name: str):
        if name not in self.properties:
            return None
        return self.properties[name]
    
    def status(self):
        """Derive a coarse outcome: aggregate children or classify ``result`` vs ``expected``."""
        if "result" not in self.properties:
            sub = [a.status() for a in self.actions]
            sub = {s for s in sub if s is not None}
            if len(sub) == 0:
                return None
            if len(sub) == 1:
                s = list(sub)[0]
                if "expected" in self.properties and s in ("sat", "unsat"):
                    return classify_expected_vs_result(
                        name=self.name,
                        expected=self.expected,
                        result=s,
                    )
                return s
            if "wrong" in sub:
                return "wrong"
            if "memout" in sub:
                return "memout"
            if "timeout" in sub:
                return "timeout"
            if "error" in sub:
                return "error"
            if "unknown" in sub:
                return "unknown"
            return "success"

        r = self.result
        if "expected" in self.properties:
            return classify_expected_vs_result(
                name=self.name,
                expected=self.expected,
                result=r,
            )
        if r in ("timeout", "memout"):
            return r
        if self.error_message:
            return "error"
        if r in ("invalid-json",) or (isinstance(r, str) and r.startswith("error")):
            return "error"
        return r

    
    def as_dict(self):
        """Serialize properties, timing fields, and nested ``actions`` for JSON dumps."""
        return {
            **self.properties,
            "enter_time": self.enter_time,
            "exit_time": self.exit_time,
            "running_time": self.running_time,
            "actions": self.actions,
        }
