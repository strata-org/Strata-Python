# @dataclass field type not asserted after access — `p.x + p.y` has unknown-
# tag operands; needs `isfrom_int` after read
"""
@dataclass field type not used in operator dispatch after access.

When reading a field from a @dataclass instance, the result is an
unconstrained Any value from DictStrAny. The declared field type
(e.g., `x: int`) is not emitted as a tag assertion after the read.

    @dataclass
    class Point:
        x: int
        y: int

    p = Point(3, 4)
    result = p.x + p.y  # PAdd needs to know both are from_int

Without `assert isfrom_int(p.x)` after the field read, the operator
dispatch for `p.x + p.y` has unknown-tag operands and may:
- Fall to catch-all (Hole)
- Require the solver to trace back through construction

This is distinct from:
- Finding 081 (field may not exist at all)
- Finding 141 (field access after construction — needs McCarthy axioms)
- Finding 221 (generic element types lost in containers)

This finding tests that field TYPE ANNOTATIONS must generate assertions.

Uses ONLY confirmed-accepted constructs: @dataclass, field access, arithmetic.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Measurement:
    value: float
    unit: str


def add_fields(p: Point) -> int:
    """p.x + p.y requires both to be known as int."""
    return p.x + p.y
    # CPython: 3 + 4 = 7
    # Model without field-type assertions:
    #   p.x → DictStrAny_get(attrs, "x") → Any (unknown tag)
    #   p.y → DictStrAny_get(attrs, "y") → Any (unknown tag)
    #   PAdd(Any, Any) → catch-all → Hole


def field_in_comparison(p: Point) -> bool:
    """p.x > p.y requires both to be known as int for PLt."""
    return p.x > p.y
    # CPython: 3 > 4 → False
    # Model: PGt(Any, Any) → Hole (tags unknown)


def field_in_arithmetic_chain(p: Point) -> int:
    """Multiple operations on fields."""
    return p.x * p.x + p.y * p.y
    # CPython: 9 + 16 = 25
    # Model: PMul(Any, Any) → Hole; PAdd(Hole, Hole) → Hole


def mixed_type_fields(m: Measurement) -> str:
    """Fields of different types — each needs its own assertion."""
    prefix: str = m.unit
    val: float = m.value
    return prefix + ": " + str(val)
    # Model: m.unit read → Any; needs assert isfrom_str
    #        m.value read → Any; needs assert isfrom_float


def field_passed_to_function(p: Point) -> int:
    """Field value passed as argument — callee expects int."""
    return double(p.x)
    # Model: p.x is Any; double expects from_int; type mismatch?


def double(n: int) -> int:
    return n * 2


def main() -> None:
    p: Point = Point(x=3, y=4)
    assert add_fields(p) == 7
    assert field_in_comparison(p) == False
    assert field_in_arithmetic_chain(p) == 25
    m: Measurement = Measurement(value=3.14, unit="meters")
    assert mixed_type_fields(m) == "meters: 3.14"
    assert field_passed_to_function(p) == 6
