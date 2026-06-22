"""Subprocess I/O with line-based tee of stderr, capture, and graceful timeout."""
import select
import subprocess
import sys
import time
from typing import TextIO


def _pump_pipes(
    proc: subprocess.Popen,
    stdout_chunks: list[str],
    stderr_chunks: list[str],
    *,
    wait: float,
) -> None:
    streams: list[tuple[TextIO, list[str], bool]] = []
    if proc.stdout is not None:
        streams.append((proc.stdout, stdout_chunks, False))
    if proc.stderr is not None:
        streams.append((proc.stderr, stderr_chunks, True))
    if not streams:
        if wait > 0:
            time.sleep(wait)
        return

    readable, _, _ = select.select([s for s, _, _ in streams], [], [], wait)
    for stream in readable:
        line = stream.readline()
        if not line:
            continue
        for s, chunks, tee_stderr in streams:
            if s is stream:
                chunks.append(line)
                if tee_stderr:
                    sys.stderr.write(line)
                    sys.stderr.flush()
                break


def _drain_pipes(
    proc: subprocess.Popen,
    stdout_chunks: list[str],
    stderr_chunks: list[str],
) -> None:
    while True:
        before = len(stdout_chunks) + len(stderr_chunks)
        _pump_pipes(proc, stdout_chunks, stderr_chunks, wait=0.1)
        if len(stdout_chunks) + len(stderr_chunks) == before:
            break


def communicate_with_timeout(
    proc: subprocess.Popen,
    timeout: float,
    term_grace: float = 5.0,
) -> tuple[str | None, str | None, bool]:
    """Wait for ``proc`` up to ``timeout`` seconds, then SIGTERM (with grace) before SIGKILL."""
    stdout_chunks: list[str] = []
    stderr_chunks: list[str] = []
    timed_out = False
    deadline = time.monotonic() + timeout

    while proc.poll() is None:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            timed_out = True
            proc.terminate()
            try:
                proc.wait(timeout=term_grace)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            break
        _pump_pipes(proc, stdout_chunks, stderr_chunks, wait=min(0.2, remaining))

    _drain_pipes(proc, stdout_chunks, stderr_chunks)

    stdout = "".join(stdout_chunks) if stdout_chunks else None
    stderr = "".join(stderr_chunks) if stderr_chunks else None
    return stdout, stderr, timed_out
