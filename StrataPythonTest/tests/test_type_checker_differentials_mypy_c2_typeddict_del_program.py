# TypedDict `'x' in p` narrowing invalidated by `del p['x']` through function
# call. Produces KeyError.
"""
c2_typeddict_del.py — TypedDict 'in' narrowing invalidated by del through function call.

No union types on fields. No inheritance. Just TypedDict with optional keys.

mypy --strict: Success (0 errors)
Runtime: KeyError
"""
from typing import TypedDict

class Point(TypedDict, total=False):
    x: int
    y: int

def remove_x(p: Point) -> None:
    if "x" in p:
        del p["x"]

def main() -> None:
    pt: Point = {"x": 1, "y": 2}
    if "x" in pt:
        remove_x(pt)  # deletes pt["x"]
        val: int = pt["x"]  # mypy: OK ('in' narrowing). Runtime: KeyError
        assert isinstance(val, int)

if __name__ == "__main__":
    main()
