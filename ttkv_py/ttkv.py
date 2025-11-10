"""Time Traveling Key-Value Store"""

from pickle import dumps, loads
from sqlite3 import Row, connect
from time import perf_counter_ns
from typing import Any


class TTKV:
    """Time Traveling Key-Value Store

    Uses `sqlite3` and `pickle` to store things.
    Could raise weird `pickle` errors with strange input.
    """

    def __init__(self) -> None:
        self.conn = connect(":memory:")
        self.conn.row_factory = Row
        self.cursor = self.conn.cursor()
        self.cursor.execute(
            "create table ttkv (ts timestamp primary key, k blob not null, v blob not null)"
        )
        self.cursor.execute("create index key_index on ttkv(k)")
        self.conn.commit()

    def put(self, key: Any, value: Any) -> None:
        """Insert a (key ↦ value) pair"""
        self.cursor.execute(
            "insert into ttkv values (?, ?, ?)",
            (perf_counter_ns(), dumps(key), dumps(value)),
        )

    def get(self, key: Any, timestamp: int | None = None) -> Any:
        """Retrieve a value for a given key

        If `timestamp` is `None`, return the latest value.
        If not, give the value at that time (up to & including it).

        Raises
        ------
        KeyError
            If `key` isn't present (or wasn't, if using a timestamp).

        ValueError
            If timestamp is not `None` and not an integer.
        """
        select = "select * from ttkv where k = ?"
        order = "order by ts desc"
        if timestamp is None:
            self.cursor.execute(f"{select} {order}", (dumps(key),))
        elif isinstance(timestamp, int):
            self.cursor.execute(
                f"{select} and ts <= ? {order}", (dumps(key), timestamp)
            )
        else:
            raise ValueError(timestamp)
        result = self.cursor.fetchone()
        if result is None:
            raise KeyError(key)
        return loads(result["v"])

    def times(self, key: Any | None = None) -> list[int]:
        """All times (or just for a given key) in our TTKV"""
        select = "select ts from ttkv"
        order = "order by ts desc"
        if key is None:
            self.cursor.execute(f"{select} {order}")
        else:
            self.cursor.execute(f"{select} where k = ? {order}", (dumps(key),))
        return [row["ts"] for row in self.cursor.fetchall()]
