# `isinstance(None, SomeClass)` — classname check on from_None() is undefined;
# must guard with isfrom_ClassInstance first
"""
isinstance ON None VALUE — MUST RETURN False FOR ALL NON-NoneType CHECKS

CPython: isinstance(None, int) → False
         isinstance(None, str) → False
         isinstance(None, SomeClass) → False

Model:   isinstance translates to tag check: isfrom_int(x), isfrom_str(x), etc.
         For from_None(), ALL these checks correctly return False.
         BUT: isinstance(x, SomeClass) translates to classname check:
              classname(x) == "SomeClass"
         For from_None(), there IS no classname field — the value is not
         a ClassInstance at all. The model may:
         - Crash (access classname on non-ClassInstance tag)
         - Return Hole (undefined behavior)
         - Return True (if classname check is vacuously satisfied)

This matters for Optional[MyClass] patterns where isinstance is used
to narrow before field access.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def is_point(val: object) -> bool:
    return isinstance(val, Point)


def safe_distance(p: object) -> int:
    """Pattern: isinstance guard before field access on Optional-like value."""
    if isinstance(p, Point):
        return p.x * p.x + p.y * p.y
    return -1


def classify_value(x: object) -> str:
    """isinstance chain where None must fail ALL checks."""
    if isinstance(x, int):
        return "int"
    elif isinstance(x, str):
        return "str"
    elif isinstance(x, Point):
        return "point"
    else:
        return "other"


def main() -> None:
    # Test 1: isinstance(None, Point) must be False
    # CPython: False
    # Model: classname check on from_None() — undefined behavior
    assert not isinstance(None, Point)

    # Test 2: isinstance(None, int) must be False
    # CPython: False
    # Model: isfrom_int(from_None()) → False (correct IF tag check works)
    assert not isinstance(None, int)

    # Test 3: safe_distance with None
    # CPython: returns -1 (isinstance fails, else branch taken)
    # Model: if isinstance check on None is Hole/True, may enter if-branch
    #         and access .x on from_None() → crash or Hole
    result: int = safe_distance(None)
    assert result == -1

    # Test 4: safe_distance with actual Point
    p: Point = Point(3, 4)
    assert safe_distance(p) == 25

    # Test 5: classify None
    # CPython: "other"
    # Model: if any isinstance check returns True for None → wrong branch
    assert classify_value(None) == "other"

    # Test 6: isinstance on actual instances (positive cases)
    assert isinstance(Point(1, 2), Point)
    assert isinstance(42, int)
    assert isinstance("hello", str)

    print("all passed")


main()
