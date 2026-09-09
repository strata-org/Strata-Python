# `isinstance` narrowing doesn't enable subclass field access — after
# narrowing, subclass-specific fields remain inaccessible to type checker
"""
After `isinstance(x, Dog)` succeeds, CPython knows `x` is a Dog and
allows access to Dog-specific fields like `x.breed`. In the Laurel
model, isinstance narrowing (finding 027) may update the classname
check, but the DictStrAny field schema used for attribute access may
still be restricted to the parent class's declared fields. The model
must allow access to subclass-specific fields after isinstance narrowing.
"""
from dataclasses import dataclass


@dataclass
class Shape:
    name: str

    def area(self: "Shape") -> int:
        return 0


@dataclass
class Rectangle(Shape):
    width: int
    height: int

    def area(self: "Rectangle") -> int:
        return self.width * self.height


@dataclass
class Circle(Shape):
    radius: int

    def area(self: "Circle") -> int:
        return 3 * self.radius * self.radius


def describe_shape(s: Shape) -> str:
    if isinstance(s, Rectangle):
        # After narrowing: s is known to be Rectangle
        # CPython: s.width and s.height are accessible
        return s.name + " " + str(s.width) + "x" + str(s.height)
    if isinstance(s, Circle):
        # After narrowing: s is known to be Circle
        # CPython: s.radius is accessible
        return s.name + " r=" + str(s.radius)
    return s.name + " unknown"


def total_perimeter(shapes: list[Shape]) -> int:
    total: int = 0
    for s in shapes:
        if isinstance(s, Rectangle):
            # Access subclass fields after narrowing
            total = total + 2 * (s.width + s.height)
        elif isinstance(s, Circle):
            total = total + 6 * s.radius  # approximate 2*pi*r
    return total


def main() -> None:
    r: Rectangle = Rectangle(name="box", width=3, height=4)
    c: Circle = Circle(name="disc", radius=5)

    # Direct access on subclass type: works trivially
    assert r.width == 3
    assert c.radius == 5

    # Access through parent type after isinstance narrowing
    d1: str = describe_shape(r)
    # CPython: "box 3x4" (accesses width, height after isinstance)
    assert d1 == "box 3x4"

    d2: str = describe_shape(c)
    # CPython: "disc r=5" (accesses radius after isinstance)
    assert d2 == "disc r=5"

    shapes: list[Shape] = [r, c]
    p: int = total_perimeter(shapes)
    # CPython: 2*(3+4) + 6*5 = 14 + 30 = 44
    assert p == 44

    print(d1, d2, p)


main()
