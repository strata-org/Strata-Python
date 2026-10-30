# Each clause calls a builtin that PySpec reads as the builtin's meaning, but the module binds
# that name, so CPython calls the module's value.
from re import compile
from typing import Any, List

len = int

def module_alias_len(s: str) -> None:
    assert len(s) >= 1, "s is not empty"

def regex_none(s: str) -> None:
    assert compile("a+").search(s) is None, "no a"

def regex_some(s: str) -> None:
    assert compile("a+").search(s) is not None, "some a"

def uses_isinstance(x: Any) -> None:
    assert isinstance(x, int), "x is an int"

def uses_all(xs: List[int]) -> None:
    assert all(x > 0 for x in xs), "xs are positive"

def uses_any(xs: List[int]) -> None:
    assert any(x > 0 for x in xs), "some x is positive"

def compile(p: str) -> int:
    ...

def isinstance(x: Any, t: Any) -> bool:
    ...

def all(xs: Any) -> bool:
    ...

def any(xs: Any) -> bool:
    ...
