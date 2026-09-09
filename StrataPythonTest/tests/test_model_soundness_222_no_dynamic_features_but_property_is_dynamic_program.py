# @property is a descriptor not in instance dict — `obj.prop` must translate
# to function call, not DictStrAny_get
"""
The subset says "no dynamic features" but `@property` IS in the subset:
  "@property for read-only computed attributes" is IN.

A @property is a DESCRIPTOR — it's looked up on the CLASS, not the
instance dict. When you access `obj.area`, Python doesn't look in
obj.__dict__["area"]. It finds the property descriptor on the class
and calls its __get__ method.

Finding 038 identified this. Under `from_ClassInstance(name, attrs)`,
field access is `DictStrAny_get(attrs, "area")`. But "area" is NOT
in the instance attrs — it's a computed property on the class.

The model must handle @property differently from regular fields.

Uses ONLY confirmed-accepted constructs: @dataclass, @property, int.
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


def use_property() -> int:
    r: Rectangle = Rectangle(width=5, height=3)
    return r.area  # 15 — calls the property getter


def property_in_expression() -> int:
    r: Rectangle = Rectangle(width=4, height=6)
    return r.area + r.perimeter  # 24 + 20 = 44


def property_in_condition() -> bool:
    r: Rectangle = Rectangle(width=5, height=5)
    return r.is_square  # True


def property_on_different_instances() -> int:
    r1: Rectangle = Rectangle(width=3, height=4)
    r2: Rectangle = Rectangle(width=5, height=5)
    return r1.area + r2.area  # 12 + 25 = 37


def main() -> None:
    assert use_property() == 15
    assert property_in_expression() == 44
    assert property_in_condition() == True
    assert property_on_different_instances() == 37

    print(use_property(), property_in_expression(),
          property_on_different_instances())


main()
