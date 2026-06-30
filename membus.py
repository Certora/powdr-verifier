#!/usr/bin/env python3
"""membus — examine / extract / align memory-bus interactions in powdr APC dumps.

Thin entry point. Run `membus.py --agent` for the agent-oriented guide, or
`membus.py --help` for humans. Logic lives in `src/membus/`.
"""
import os
import sys

from src.membus.cli import main

if __name__ == "__main__":
    try:
        sys.exit(main())
    except BrokenPipeError:
        # stdout closed early (e.g. piped into `head`); silence the flush-on-exit
        # error by redirecting fd 1 to devnull, then exit cleanly.
        os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        sys.exit(0)
