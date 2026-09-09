# `@property` attributes are descriptors on the class, not in instance dict —
# model reads from DictStrAny and finds nothing
"""
@property creates a descriptor on the class, not a field in the instance dict.
Accessing obj.prop calls the getter function. The model reads from
instance_attributes (DictStrAny) where the property does NOT exist —
returning Hole or raising a missing-key error instead of calling the getter.
"""
from dataclasses import dataclass


class Rectangle:
    def __init__(self, width: int, height: int) -> None:
        self.width = width
        self.height = height

    @property
    def area(self) -> int:
        return self.width * self.height

    @property
    def perimeter(self) -> int:
        return 2 * (self.width + self.height)


def total_area(r1: Rectangle, r2: Rectangle) -> int:
    return r1.area + r2.area


def main() -> None:
    r: Rectangle = Rectangle(width=3, height=4)

    # @property access — calls the getter, not a field read
    assert r.area == 12
    assert r.perimeter == 14

    r2: Rectangle = Rectangle(width=5, height=6)
    t: int = total_area(r, r2)
    assert t == 42  # 12 + 30

    print(r.area, r.perimeter, t)


main()
