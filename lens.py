#!/usr/bin/env python3
"""lens — statistics over powdr APC JSON dumps.

Thin entry point, equivalent to the ``lens`` console script (see
``[project.scripts]`` in pyproject.toml). Run `lens.py --agent` for the
agent-oriented guide, or `lens.py --help` for humans. Logic lives in
`src/lens/`.
"""
import sys

from src.lens.cli import main

if __name__ == "__main__":
    sys.exit(main())
