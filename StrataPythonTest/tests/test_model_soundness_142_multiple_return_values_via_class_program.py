# Dataclass returned from function — caller accessing fields requires inlining
# or auto-generated postconditions
"""
Python functions can only return one value. To return multiple values,
the common pattern is to return a dataclass (or tuple — finding 028).
The model must handle: construct a dataclass inside a function, return
it, and have the caller access its fields.

This tests the full pipeline: construction → return → field access
across a function boundary.
"""
from dataclasses import dataclass


@dataclass
class Result:
    value: int
    success: bool
    message: str


@dataclass
class MinMax:
    min_val: int
    max_val: int


def safe_divide(a: int, b: int) -> Result:
    if b == 0:
        return Result(value=0, success=False, message="division by zero")
    return Result(value=a // b, success=True, message="ok")


def find_min_max(lst: list[int]) -> MinMax:
    lo: int = lst[0]
    hi: int = lst[0]
    i: int = 1
    while i < len(lst):
        if lst[i] < lo:
            lo = lst[i]
        if lst[i] > hi:
            hi = lst[i]
        i = i + 1
    return MinMax(min_val=lo, max_val=hi)


def main() -> None:
    # Return dataclass from function, access fields
    r1: Result = safe_divide(10, 3)
    assert r1.value == 3
    assert r1.success == True
    assert r1.message == "ok"

    r2: Result = safe_divide(10, 0)
    assert r2.value == 0
    assert r2.success == False

    # MinMax
    mm: MinMax = find_min_max([3, 1, 4, 1, 5, 9, 2, 6])
    assert mm.min_val == 1
    assert mm.max_val == 9

    # Use result in condition
    r3: Result = safe_divide(100, 5)
    if r3.success:
        assert r3.value == 20

    print(r1.value, r2.success, mm.min_val, mm.max_val)


main()
