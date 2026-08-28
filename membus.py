#!/usr/bin/env python3
"""membus — examine / extract / align memory-bus interactions in powdr APC dumps.

Thin entry point, equivalent to the ``membus`` console script (see
``[project.scripts]`` in pyproject.toml). Kept as a file because the verify
pipeline shells out to this path directly -- see
``src/verify/membus_subprocess.py``. Run `membus.py --agent` for the
agent-oriented guide, or `membus.py --help` for humans. Logic lives in
`src/membus/`.
"""
import sys

from src.membus.cli import console_main

if __name__ == "__main__":
    sys.exit(console_main())
