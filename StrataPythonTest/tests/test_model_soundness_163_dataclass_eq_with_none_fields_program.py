# Dataclass `__eq__` with Optional fields — cross-tag PEq needed for
# `from_None() == from_None()` and `from_None() != from_int(n)`
"""
@dataclass auto-generates __eq__ that compares fields structurally.
When a field is Optional[T], equality must handle None correctly:
  - None == None → True
  - None == some_value → False
  - some_value == None → False

The model's PEq must handle cross-tag comparison (from_None vs from_int)
correctly for dataclass equality to work. Finding 076 identified that
cross-tag PEq falls to Hole. This means @dataclass __eq__ with Optional
fields produces Hole instead of True/False.

Uses ONLY confirmed-accepted constructs: @dataclass, Optional, int, str.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class User:
    name: str
    age: Optional[int]


@dataclass
class Config:
    host: str
    port: int
    timeout: Optional[int]


def users_equal_both_none() -> bool:
    u1: User = User(name="alice", age=None)
    u2: User = User(name="alice", age=None)
    return u1 == u2  # True: same name, both age=None


def users_equal_both_set() -> bool:
    u1: User = User(name="bob", age=30)
    u2: User = User(name="bob", age=30)
    return u1 == u2  # True: same name, same age


def users_not_equal_none_vs_value() -> bool:
    u1: User = User(name="carol", age=None)
    u2: User = User(name="carol", age=25)
    return u1 == u2  # False: None != 25


def users_not_equal_different_name() -> bool:
    u1: User = User(name="dave", age=40)
    u2: User = User(name="eve", age=40)
    return u1 == u2  # False: different name


def config_equality() -> bool:
    c1: Config = Config(host="localhost", port=8080, timeout=None)
    c2: Config = Config(host="localhost", port=8080, timeout=None)
    c3: Config = Config(host="localhost", port=8080, timeout=30)
    return c1 == c2 and c1 != c3


def main() -> None:
    assert users_equal_both_none() == True
    assert users_equal_both_set() == True
    assert users_not_equal_none_vs_value() == False
    assert users_not_equal_different_name() == False
    assert config_equality() == True

    print(users_equal_both_none(), users_not_equal_none_vs_value(),
          config_equality())


main()
