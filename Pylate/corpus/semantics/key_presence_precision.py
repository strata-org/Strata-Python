# Key-presence precision: a mapping read whose key the per-key cells prove
# present must not admit KeyError, and one that cannot be proven present
# must keep it. Every function is checked against CPython.
from typing import TypedDict, NotRequired

class Shape(TypedDict):
    a: int
    b: str
    c: NotRequired[int]

def plain_literal(flag: bool) -> int:
    d = {"k": 1, "j": 2}
    return d["k"]

def plain_get(flag: bool) -> int:
    d = {"k": 1}
    return d.get("k")

def plain_dynamic(flag: bool) -> int:
    d = {"a": 1, "b": 2}
    key = "a" if flag else "b"
    return d[key]

def plain_dynamic_partial(flag: bool) -> int:
    d = {"a": 1}
    key = "a" if flag else "zz"
    return d[key]

def td_literal(s: Shape) -> int:
    return s["a"]

def td_dynamic(s: Shape, flag: bool) -> object:
    key = "a" if flag else "b"
    return s[key]

def td_notrequired(s: Shape) -> int:
    return s["c"]

def plain_after_clear(flag: bool) -> int:
    d = {"k": 1}
    d.clear()
    return d["k"]

def plain_pop(flag: bool) -> int:
    d = {"k": 1}
    return d.pop("k")

def plain_membership(flag: bool) -> bool:
    d = {"k": 1}
    return "k" in d
