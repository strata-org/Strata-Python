# A call that PySpec reads as its builtin's meaning, but that names a parameter or passes
# keyword arguments, means something else in CPython: its assert is recorded as dropped.
from re import compile
from typing import Any, Dict, List

def len_kw(s: str) -> None:
    assert len(s, x=1) >= 1, "s is not empty"

def isinstance_kw(x: Any) -> None:
    assert isinstance(x, int, y=2), "x is an int"

def regex_flags(s: str) -> None:
    assert not (compile("a", flags=2).search(s) is not None), "s has no a"

def regex_pos(s: str) -> None:
    if compile("a").search(s, pos=1) is not None:
        assert len(s) >= 5, "long"

def all_kw(xs: List[int]) -> None:
    assert all((x > 0 for x in xs), y=1), "xs are positive"


def param_len(s: str, len: Any) -> None:
    assert len(s) >= 1, "s is not empty"

def param_isinstance(x: Any, isinstance: Any) -> None:
    assert isinstance(x, int), "x is an int"

def param_all(xs: List[int], all: Any) -> None:
    assert all(x > 0 for x in xs), "xs are positive"


def param_type(x: Any, str: Any) -> None:
    assert isinstance(x, str), "x is a str"

def view_kw(d: Dict[str, int]) -> None:
    assert all(k != "" for k in d.keys(x=1)), "no key is empty"

def loop_view_kw(d: Dict[str, int]) -> None:
    for k in d.keys(x=1):
        assert k != "", "no key is empty"

@admit(lambda s, result: len(s, x=1) >= 1)
def admit_kw(s: str) -> int:
    ...

@admit(lambda s, len, result: len(s) >= 1)
def admit_param_len(s: str, len: Any) -> int:
    ...

@invariant(lambda self: len(self.xs, k=1) > 0)
class Box:
    xs: List[int]
