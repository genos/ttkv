from datetime import datetime, UTC
from pathlib import Path
from typing import Any

from dill import dumps, loads
from sqlalchemy.engine import Engine
from sqlmodel import Field, Session, SQLModel, create_engine, select, desc


class TTKV(SQLModel, table=True):
    id: int | None = Field(default=None, primary_key=True)
    key: bytes = Field(index=True)
    value: bytes
    timestamp: datetime


def create(path: Path | None = None, is_new: bool = True) -> Engine:
    engine = create_engine("sqlite:///:memory:" if path is None else f"sqlite://{path}")
    if is_new:
        SQLModel.metadata.create_all(engine)
    return engine


def put(engine: Engine, key: Any, value: Any, timestamp: datetime | None = None):
    if timestamp is None:
        timestamp = datetime.now(UTC)
    with Session(engine) as s:
        s.add(TTKV(key=dumps(key), value=dumps(value), timestamp=timestamp))
        s.commit()


def get(engine: Engine, key: Any, timestamp: datetime | None = None) -> Any | None:
    with Session(engine) as s:
        statement = select(TTKV.value).where(TTKV.key == dumps(key))
        if timestamp is not None:
            statement = statement.where(TTKV.timestamp <= timestamp)
        statement = statement.order_by(desc(TTKV.timestamp))
        value = s.exec(statement).first()
    return None if value is None else loads(value)


def times(engine: Engine, key: Any | None = None) -> list[datetime]:
    with Session(engine) as s:
        statement = select(TTKV.timestamp)
        if key is not None:
            statement = statement.where(TTKV.key == dumps(key))
        statement = statement.order_by(desc(TTKV.timestamp))
        return list(s.exec(statement).all())
