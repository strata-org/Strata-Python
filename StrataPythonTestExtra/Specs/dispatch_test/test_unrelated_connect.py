from typing import Any


def user_call() -> Any:
    db_conn: Any = 42
    return db_conn.connect("localhost")
