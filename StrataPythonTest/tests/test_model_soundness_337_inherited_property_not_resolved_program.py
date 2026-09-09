# Inherited @property not resolved on child — property lookup uses child
# classname; parent's property getter never found
"""
INHERITED @property NOT RESOLVED ON CHILD CLASS

CPython: Child inherits parent's @property; child.prop calls parent's getter.
Model:   Method/property lookup uses classname string; child's classname doesn't
         match parent's method table → property call fails or returns Hole.

This is related to finding 313 (inherited method not found on child) but
specifically for @property, which has ADDITIONAL complexity: the property
must be translated as a function call, not a field read (finding 222).
When inheritance is involved, the translator must resolve the property
getter through the class hierarchy.
"""
from dataclasses import dataclass


class Shape:
    def __init__(self: "Shape", name: str) -> None:
        self.name: str = name

    @property
    def description(self: "Shape") -> str:
        return self.name


class Circle(Shape):
    def __init__(self: "Circle", radius: float) -> None:
        super().__init__("circle")
        self.radius: float = radius

    @property
    def area(self: "Circle") -> float:
        return 3.14159 * self.radius * self.radius


class Rectangle(Shape):
    def __init__(self: "Rectangle", width: float, height: float) -> None:
        super().__init__("rectangle")
        self.width: float = width
        self.height: float = height

    @property
    def area(self: "Rectangle") -> float:
        return self.width * self.height

    @property
    def perimeter(self: "Rectangle") -> float:
        return 2.0 * (self.width + self.height)


def describe_shape(s: Shape) -> str:
    # Accesses inherited @property through parent-typed variable
    return s.description


def main() -> None:
    c: Circle = Circle(5.0)
    r: Rectangle = Rectangle(3.0, 4.0)

    # Test 1: property defined on own class works
    assert abs(c.area - 78.53975) < 0.001
    assert abs(r.area - 12.0) < 0.001

    # Test 2: INHERITED property accessed on child instance
    # CPython: c.description == "circle" (inherited from Shape)
    # Model: classname is "Circle", property lookup in "Circle" methods fails
    #        → Hole or DictStrAny_get on instance attrs (finds nothing)
    assert c.description == "circle"
    assert r.description == "rectangle"

    # Test 3: through parent-typed variable
    # CPython: describe_shape(c) == "circle"
    # Model: s has classname "Circle" but function expects Shape;
    #        property resolution on Shape.description may work,
    #        but if dispatch uses runtime classname → fails
    assert describe_shape(c) == "circle"
    assert describe_shape(r) == "rectangle"

    print(c.description)
    print(r.description)


main()
