# @property computed value — `r.area` must call getter function, not
# DictStrAny_get; "area" not in instance dict → Hole
"""
@property COMPUTED VALUE — NOT IN INSTANCE DICT

CPython: class Rectangle:
             @property
             def area(self) -> int: return self.width * self.height
         r = Rectangle(3, 4); r.area → 12

Model:   r.area translates to:
         DictStrAny_get(instance_attributes(r), "area")
         → Hole (no "area" key in the dict — it's a property, not a field!)

         @property creates a DESCRIPTOR on the CLASS, not an attribute
         on the INSTANCE. The instance dict only has width and height.
         Accessing .area must CALL the getter function, not read the dict.

CPython result: 12
Model result: Hole (key "area" not in instance_attributes)

Root cause: Finding 222 identified this. Property access must translate
to a function call, not a DictStrAny_get.
"""
from dataclasses import dataclass


@dataclass
class Rectangle:
    width: int
    height: int

    @property
    def area(self: "Rectangle") -> int:
        return self.width * self.height

    @property
    def perimeter(self: "Rectangle") -> int:
        return 2 * (self.width + self.height)

    @property
    def is_square(self: "Rectangle") -> bool:
        return self.width == self.height


@dataclass
class Circle:
    radius: float

    @property
    def area(self: "Circle") -> float:
        return 3.14159 * self.radius * self.radius

    @property
    def diameter(self: "Circle") -> float:
        return 2.0 * self.radius


def main() -> None:
    # Test 1: property computes from fields
    r: Rectangle = Rectangle(3, 4)
    assert r.area == 12
    assert r.perimeter == 14

    # Test 2: property returns bool
    assert not r.is_square
    sq: Rectangle = Rectangle(5, 5)
    assert sq.is_square

    # Test 3: float property
    c: Circle = Circle(5.0)
    assert abs(c.area - 78.53975) < 0.001
    assert c.diameter == 10.0

    # Test 4: property on different instances
    r2: Rectangle = Rectangle(10, 2)
    assert r2.area == 20
    assert r.area == 12  # original unchanged

    print("all passed")


main()
