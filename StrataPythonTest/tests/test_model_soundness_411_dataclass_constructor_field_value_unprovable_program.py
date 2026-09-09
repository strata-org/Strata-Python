# `Point(3,4).x == 3` unprovable — constructor stores to DictStrAny but get
# has no read-over-write axiom; MOST BASIC dataclass operation fails
"""
DATACLASS CONSTRUCTOR — FIELD VALUE UNPROVABLE AFTER CONSTRUCTION

CPython: p = Point(3, 4); p.x == 3 → True (always)

Model:   Point(3, 4) translates to:
           from_ClassInstance("Point", DictStrAny_set(DictStrAny_set(empty, "x", 3), "y", 4))
         p.x translates to:
           DictStrAny_get(instance_attributes(p), "x")

         Without McCarthy axiom get(set(d, k, v), k) == v:
           DictStrAny_get(DictStrAny_set(..., "x", 3), "x") == ???
           → UNPROVABLE

CPython result: 3
Model result: unconstrained (Hole)

Root cause: DictStrAny_get and DictStrAny_set are uninterpreted functions
with no read-over-write axiom (findings 093/141/254).
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Config:
    host: str
    port: int
    timeout: int


def construct_and_read() -> bool:
    """Simplest case: construct, immediately read field."""
    p: Point = Point(3, 4)
    # CPython: p.x == 3 (trivially true)
    # Model: DictStrAny_get(set(set(empty,"x",3),"y",4), "x") == 3
    #         → needs McCarthy axiom: get(set(d,k,v),k) == v
    return p.x == 3 and p.y == 4


def construct_and_use_in_arithmetic() -> int:
    """Use field value in computation."""
    p: Point = Point(5, 12)
    # p.x*p.x + p.y*p.y should be 25 + 144 = 169
    return p.x * p.x + p.y * p.y


def construct_three_fields() -> bool:
    """Three fields — each must be independently readable."""
    cfg: Config = Config("localhost", 8080, 30)
    return cfg.host == "localhost" and cfg.port == 8080 and cfg.timeout == 30


def construct_and_pass(x: int, y: int) -> int:
    """Construct with variables, read back."""
    p: Point = Point(x, y)
    # p.x == x must be provable (not just for literals)
    return p.x + p.y


def main() -> None:
    assert construct_and_read()
    assert construct_and_use_in_arithmetic() == 169
    assert construct_three_fields()
    assert construct_and_pass(7, 8) == 15

    print("all passed")


main()
