import json
import os
from pathlib import Path
import time

class Action:
    def __init__(self, name: str, **kwargs):
        self.enter_time = kwargs.pop("enter_time", None)
        self.exit_time = kwargs.pop("exit_time", None)
        self.running_time = kwargs.pop("running_time", None)
        self.actions = kwargs.pop("actions", [])
        self.properties = kwargs | { "name": name }

    def __enter__(self):
        self.enter_time = time.perf_counter_ns()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.exit_time = time.perf_counter_ns()
        self.running_time = (self.exit_time - self.enter_time) / 1000000000
    
    def action(self, name: str, **kwargs):
        action = Action(name, **kwargs)
        self.actions.append(action)
        return action
    
    def add_action(self, action: "Action"):
        self.actions.append(action)
    
    def __iadd__(self, kwargs):
        if isinstance(kwargs, dict):
            self.properties.update(kwargs)
        elif isinstance(kwargs, tuple):
            assert len(kwargs) == 2
            assert kwargs[0] in self.properties
            self.properties[kwargs[0]].append(kwargs[1])
        else:
            raise ValueError(f"Invalid argument type: {type(kwargs)}")

        return self
    
    def __getattr__(self, name: str):
        return self.properties[name]
    
    def as_dict(self):
        return {
            **self.properties,
            "enter_time": self.enter_time,
            "exit_time": self.exit_time,
            "running_time": self.running_time,
            "actions": self.actions,
        }
