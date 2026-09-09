# **PROMISE vs DELIVERY**: isinstance on user classes is IN but model uses
# exact classname match; `isinstance(child, Parent)` fails
"""
SUBSET PROMISES isinstance ON USER CLASSES — MODEL CAN'T DO IT

The subset says isinstance is IN for user classes:
  "isinstance(x, T) for T ∈ {int, float, str, bool, list, dict, tuple, <user class>}"

But findings 027/172/219 show the model CANNOT do isinstance on user
classes correctly because:
1. classname string has no hierarchy (finding 172)
2. isinstance(child, Parent) fails — exact match only (finding 027)
3. The subset allows inheritance + isinstance but model has no MRO (finding 219)

This is a PROMISE vs DELIVERY gap: the subset says "we support isinstance
on user classes" but the model can only check exact classname equality.
"""
from dataclasses import dataclass


class Shape:
    def __init__(self: "Shape", name: str) -> None:
        self.name: str = name


class Circle(Shape):
    def __init__(self: "Circle", radius: float) -> None:
        super().__init__("circle")
        self.radius: float = radius


class Rectangle(Shape):
    def __init__(self: "Rectangle", w: float, h: float) -> None:
        super().__init__("rectangle")
        self.width: float = w
        self.height: float = h


def is_shape(obj: object) -> bool:
    """isinstance with parent class — needs hierarchy."""
    return isinstance(obj, Shape)


def area(s: Shape) -> float:
    """isinstance narrowing to access subclass fields."""
    if isinstance(s, Circle):
        return 3.14159 * s.radius * s.radius
    elif isinstance(s, Rectangle):
        return s.width * s.height
    return 0.0


def filter_circles(shapes: list[Shape]) -> list[Circle]:
    """Filter by isinstance — common pattern."""
    result: list[Circle] = []
    for s in shapes:
        if isinstance(s, Circle):
            result.append(s)
    return result


def main() -> None:
    c: Circle = Circle(5.0)
    r: Rectangle = Rectangle(3.0, 4.0)

    # Test 1: isinstance with PARENT class
    # CPython: isinstance(Circle(...), Shape) → True
    # Model: classname(c) == "Shape" → False (exact match!) — WRONG
    assert is_shape(c)
    assert is_shape(r)

    # Test 2: isinstance narrowing for field access
    assert abs(area(c) - 78.53975) < 0.01
    assert abs(area(r) - 12.0) < 0.01

    # Test 3: filter by type
    shapes: list[Shape] = [c, r, Circle(2.0)]
    circles: list[Circle] = filter_circles(shapes)
    assert len(circles) == 2

    print("all passed")


main()
