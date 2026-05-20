import sqlite3
from pathlib import Path
from typing import TYPE_CHECKING, Any, Optional, Sequence

if TYPE_CHECKING:
    from .render import TreeNode

__DB: Optional[sqlite3.Connection] = None


def connect_db(uri: Path | str) -> sqlite3.Connection:
    global __DB
    if __DB is not None:
        __DB.close()
    if isinstance(uri, Path):
        uri.parent.mkdir(parents=True, exist_ok=True)
    __DB = sqlite3.connect(uri if isinstance(uri, str) else str(uri))
    __DB.execute("PRAGMA foreign_keys = ON")
    return __DB


def close_db() -> None:
    global __DB
    if __DB is not None:
        __DB.close()
        __DB = None

def create_db() -> None:
    assert __DB is not None
    __DB.execute("DROP TABLE IF EXISTS substeps")
    __DB.execute("DROP TABLE IF EXISTS verification_steps")
    __DB.execute(
        """
        CREATE TABLE verification_steps (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            input1 TEXT NOT NULL,
            input2 TEXT NOT NULL,
            size_bytes INTEGER,
            block INTEGER,
            passname TEXT,
            running_time REAL,
            result TEXT,
            status TEXT,
            UNIQUE(input1, input2)
        )
        """
    )
    __DB.execute(
        """
        CREATE TABLE substeps (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            verification_step_id INTEGER NOT NULL,
            parent INTEGER,
            name TEXT NOT NULL,
            running_time REAL,
            result TEXT,
            expected TEXT,
            status TEXT,
            FOREIGN KEY (verification_step_id) REFERENCES verification_steps(id) ON DELETE CASCADE,
            FOREIGN KEY (parent) REFERENCES substeps(id) ON DELETE CASCADE
        )
        """
    )
    __DB.execute("CREATE INDEX idx_verification_steps_block ON verification_steps(block)")
    __DB.execute(
        "CREATE INDEX idx_substeps_verification_step_id ON substeps(verification_step_id)"
    )
    __DB.execute("CREATE INDEX idx_substeps_parent ON substeps(parent)")
    __DB.commit()


def clear_verification_steps() -> None:
    assert __DB is not None
    __DB.execute("DELETE FROM verification_steps")


def insert_verification_row(i1, i2, val) -> int:
    assert __DB is not None
    p1, p2 = str(Path(i1).resolve()), str(Path(i2).resolve())
    try:
        size_bytes = Path(p1).stat().st_size + Path(p2).stat().st_size
    except OSError:
        size_bytes = None
    if isinstance(val, tuple):
        block, passname = val
        cur = __DB.execute(
            """
            INSERT INTO verification_steps (
                input1, input2, size_bytes, block, passname, running_time, result, status
            ) VALUES (?, ?, ?, ?, ?, NULL, NULL, NULL)
            """,
            (p1, p2, size_bytes, block, passname),
        )
    else:
        cur = __DB.execute(
            """
            INSERT INTO verification_steps (
                input1, input2, size_bytes, block, passname, running_time, result, status
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                p1,
                p2,
                size_bytes,
                val.block,
                val.passname,
                val.running_time,
                val.result,
                val.status,
            ),
        )
    return int(cur.lastrowid)


def insert_substeps(verification_step_id: int, steps: Sequence["TreeNode"]) -> None:
    assert __DB is not None
    for step in steps:
        _insert_substep(verification_step_id, step, parent=None)


def _insert_substep(
    verification_step_id: int,
    step: "TreeNode",
    parent: int | None,
) -> int:
    assert __DB is not None
    cur = __DB.execute(
        """
        INSERT INTO substeps (
            verification_step_id, parent, name, running_time, result, expected, status
        )
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            verification_step_id,
            parent,
            step.name,
            step.running_time,
            step.result,
            step.expected,
            step.status,
        ),
    )
    substep_id = int(cur.lastrowid)
    for child in step.children:
        _insert_substep(
            verification_step_id,
            child,
            parent=substep_id,
        )
    return substep_id


def commit_db() -> None:
    assert __DB is not None
    __DB.commit()


def query(sql: str, parameters: Sequence[Any] = ()) -> list[tuple[Any, ...]]:
    assert __DB is not None
    return list(__DB.execute(sql, parameters).fetchall())


def query_single_value(sql: str, parameters: Sequence[Any] = ()) -> Any:
    assert __DB is not None
    row = __DB.execute(sql, parameters).fetchone()
    return None if row is None else row[0]
