#!/usr/bin/env python3
"""membus — examine / extract / align memory-bus interactions in powdr APC dumps.

Thin entry point. Run `membus.py --agent` for the agent-oriented guide, or
`membus.py --help` for humans. Logic lives in `src/membus/`.
"""
import sys

from src.membus.cli import main

if __name__ == "__main__":
    sys.exit(main())
