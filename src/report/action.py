"""Hierarchical run record: timing, nested sub-actions, and JSON-serializable properties."""
import json
import os
from pathlib import Path
import time

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
        """Derive a coarse outcome: aggregate children or compare ``result`` to ``expected``."""
        if "result" not in self.properties:
            sub = [ a.status() for a in self.actions ]
            sub = { s for s in sub if s is not None }
            if len(sub) == 0:
                return None
            if len(sub) == 1:
                return list(sub)[0]
            if "error" in sub:
                return "error"
            if "wrong" in sub:
                return "wrong"
            if "timeout" in sub:
                return "timeout"
            if "unknown" in sub:
                return "unknown"
            return "success"

        if self.name != "isqf" and "expected" in self.properties:
            if self.result == self.expected:
                return "success"
            return "error"
        return self.result

    
    def as_dict(self):
        """Serialize properties, timing fields, and nested ``actions`` for JSON dumps."""
        return {
            **self.properties,
            "enter_time": self.enter_time,
            "exit_time": self.exit_time,
            "running_time": self.running_time,
            "actions": self.actions,
        }
