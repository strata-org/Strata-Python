# Value sem: object param field write lost — `f(obj); obj.x=99` inside f
# invisible; CPython: obj.x==99, Model: obj.x==0
"""
VALUE SEMANTICS WHERE CPYTHON HAS REFERENCE SEMANTICS:
Object passed to function — function writes field, caller sees in CPython.

CPython: object param is a reference. obj.x = v mutates the SAME object.
Model: object param is a COPY. obj.x = v rebuilds the copy. Caller unchanged.

CPython result: p.x == 99
Model result:  p.x == 0
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def set_x(p: Point, val: int) -> None:
    p.x = val


def main() -> None:
    point: Point = Point(x=0, y=0)
    set_x(point, 99)

    # CPython: point.x is 99 — function mutated the SAME object
    # Model:  point.x is 0  — function mutated a COPY
    assert point.x == 99  # True in CPython

    print(point.x, point.y)


main()
