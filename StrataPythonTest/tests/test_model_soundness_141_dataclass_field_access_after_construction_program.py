# Dataclass field access after construction — `Point(x=3,y=4).x == 3` requires
# McCarthy axioms (finding 093)
"""
After constructing a @dataclass instance, field access must return the
values passed to the constructor. This requires the translator to emit
postconditions connecting constructor arguments to field values.

Without this, `Point(x=3, y=4).x` is unprovable — the solver doesn't
know that constructing with x=3 means the x field contains 3.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Rectangle:
    width: int
    height: int

    def area(self: "Rectangle") -> int:
        return self.width * self.height

    def perimeter(self: "Rectangle") -> int:
        return 2 * (self.width + self.height)


def distance_sq(p1: Point, p2: Point) -> int:
    dx: int = p1.x - p2.x
    dy: int = p1.y - p2.y
    return dx * dx + dy * dy


def create_and_use() -> int:
    p: Point = Point(x=3, y=4)
    # The solver must know: p.x == 3, p.y == 4
    return p.x + p.y


def main() -> None:
    # Immediate field access after construction
    p: Point = Point(x=3, y=4)
    assert p.x == 3
    assert p.y == 4

    # Method using fields
    r: Rectangle = Rectangle(width=5, height=3)
    assert r.area() == 15
    assert r.perimeter() == 16

    # Function using constructed values
    assert create_and_use() == 7

    # Distance between two points
    p1: Point = Point(x=0, y=0)
    p2: Point = Point(x=3, y=4)
    assert distance_sq(p1, p2) == 25

    print(p.x, r.area(), distance_sq(p1, p2))


main()
