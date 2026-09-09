# Method override with no virtual dispatch — model calls parent method based
# on static type, not runtime class tag
"""
When a subclass overrides a method, calling that method on a subclass
instance should dispatch to the SUBCLASS implementation. In the Laurel
model, method calls are translated as direct function calls based on the
declared type. If the variable is typed as the parent class but holds a
subclass instance, the model calls the parent's method instead of the
child's override.
"""
from dataclasses import dataclass


@dataclass
class Shape:
    name: str

    def area(self: "Shape") -> int:
        return 0

    def describe(self: "Shape") -> str:
        return self.name + " area=" + str(self.area())


@dataclass
class Square(Shape):
    side: int

    def area(self: "Square") -> int:
        return self.side * self.side


@dataclass
class Circle(Shape):
    radius: int

    def area(self: "Circle") -> int:
        return 3 * self.radius * self.radius  # approximate


def total_area(shapes: list[Shape]) -> int:
    total: int = 0
    for s in shapes:
        total = total + s.area()
    return total


def main() -> None:
    sq: Square = Square(name="sq", side=4)
    ci: Circle = Circle(name="ci", radius=3)

    # Direct call on subclass: dispatches to override
    assert sq.area() == 16
    assert ci.area() == 27

    # Call through parent type: should STILL dispatch to override
    shapes: list[Shape] = [sq, ci]
    t: int = total_area(shapes)
    # CPython: 16 + 27 = 43 (virtual dispatch)
    # Model: 0 + 0 = 0 (calls Shape.area which returns 0)
    assert t == 43

    # describe() calls self.area() — should dispatch to override
    desc: str = sq.describe()
    # CPython: "sq area=16" (self.area() dispatches to Square.area)
    # Model: "sq area=0" (self.area() dispatches to Shape.area)
    assert desc == "sq area=16"

    print(t, desc)


main()
