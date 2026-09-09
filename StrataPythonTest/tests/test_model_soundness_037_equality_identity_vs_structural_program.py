# Default `==` on non-@dataclass classes is identity (returns False for same-
# field objects); model uses structural equality (returns True)
"""
Python's default `==` for class instances (without __eq__) is identity
comparison (`is`). Two objects with identical fields are NOT equal.
The model has no object identity — PEq on two from_ClassInstance values
with the same fields returns True (structural equality), diverging from
CPython which returns False.
"""
from dataclasses import dataclass


@dataclass
class Config:
    host: str
    port: int


class Connection:
    def __init__(self, host: str, port: int) -> None:
        self.host = host
        self.port = port


def configs_equal(a: Config, b: Config) -> bool:
    # @dataclass: __eq__ compares fields. Two Configs with same fields ARE equal.
    return a == b


def connections_equal(a: Connection, b: Connection) -> bool:
    # No @dataclass: default __eq__ is identity. Same fields does NOT mean equal.
    return a == b


def main() -> None:
    # @dataclass: structural equality (model is correct here)
    c1: Config = Config(host="localhost", port=8080)
    c2: Config = Config(host="localhost", port=8080)
    assert configs_equal(c1, c2) == True  # same fields → equal

    # Plain class: identity equality (model is WRONG here)
    conn1: Connection = Connection(host="localhost", port=8080)
    conn2: Connection = Connection(host="localhost", port=8080)
    assert connections_equal(conn1, conn2) == False  # different objects → not equal
    assert connections_equal(conn1, conn1) == True   # same object → equal

    print(configs_equal(c1, c2), connections_equal(conn1, conn2))


main()
