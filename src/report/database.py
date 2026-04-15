import sqlite3
from pathlib import Path
from typing import Any, Optional, Sequence

__DB: Optional[sqlite3.Connection] = None


def connect_db(uri: Path | str) -> sqlite3.Connection:
    global __DB
    if __DB is not None:
        __DB.close()
    __DB = sqlite3.connect(uri if isinstance(uri, str) else str(uri))
    return __DB


def close_db() -> None:
    global __DB
    if __DB is not None:
        __DB.close()
        __DB = None


def create_db() -> None:
    assert __DB is not None
    __DB.execute(
        """
        CREATE TABLE IF NOT EXISTS verification_steps (
            input1 TEXT NOT NULL,
            input2 TEXT NOT NULL,
            block INTEGER,
            passname TEXT,
            running_time REAL,
            result TEXT,
            status TEXT,
            PRIMARY KEY (input1, input2)
        )
        """
    )
    __DB.execute("CREATE INDEX IF NOT EXISTS idx_verification_steps_block ON verification_steps(block)")
    __DB.commit()


def clear_verification_steps() -> None:
    assert __DB is not None
    __DB.execute("DELETE FROM verification_steps")


def insert_verification_row(i1, i2, val) -> None:
    assert __DB is not None
    p1, p2 = str(Path(i1).resolve()), str(Path(i2).resolve())
    if isinstance(val, tuple):
        block, passname = val
        __DB.execute(
            """
            INSERT INTO verification_steps (
                input1, input2, block, passname, running_time, result, status
            ) VALUES (?, ?, ?, ?, NULL, NULL, NULL)
            """,
            (p1, p2, block, passname),
        )
    else:
        __DB.execute(
            """
            INSERT INTO verification_steps (
                input1, input2, block, passname, running_time, result, status
            ) VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            (p1, p2, val.block, val.passname, val.running_time, val.result, val.status),
        )


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
