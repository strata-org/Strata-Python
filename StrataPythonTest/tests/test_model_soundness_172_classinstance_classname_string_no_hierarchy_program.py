# `from_ClassInstance` classname string encodes no hierarchy —
# isinstance/dispatch fail for subclass through parent-typed variable
"""
`from_ClassInstance(classname: string, instance_attributes: DictStrAny)`
uses a STRING for the class name. This means:

1. isinstance(obj, Parent) checks `classname == "Parent"` — exact match
   A Dog instance has classname="Dog", so isinstance(dog, Animal) fails
   even though Dog inherits from Animal.

2. Method dispatch uses the static type's classname, not the runtime
   classname. If `animal: Animal = Dog(...)`, calling `animal.speak()`
   dispatches to Animal.speak, not Dog.speak.

3. Subclass field access: a Dog stored as `Animal` type still has
   classname="Dog" and all Dog fields, but the verifier may not know
   which fields are available without checking the classname.

Finding 027 identified isinstance. Finding 055 identified virtual dispatch.
This finding shows the ROOT CAUSE: a flat string classname cannot encode
an inheritance hierarchy.

Uses ONLY confirmed-accepted constructs: class, single inheritance, method.
"""
from dataclasses import dataclass


@dataclass
class Shape:
    x: int
    y: int

    def area(self: "Shape") -> int:
        return 0

    def describe(self: "Shape") -> str:
        return "shape"


@dataclass
class Rectangle(Shape):
    width: int
    height: int

    def area(self: "Rectangle") -> int:
        return self.width * self.height

    def describe(self: "Rectangle") -> str:
        return "rectangle"


@dataclass
class Circle(Shape):
    radius: int

    def area(self: "Circle") -> int:
        return 3 * self.radius * self.radius  # approximate

    def describe(self: "Circle") -> str:
        return "circle"


def is_shape(obj: Shape) -> bool:
    return isinstance(obj, Shape)


def get_area(s: Shape) -> int:
    """Should dispatch to the actual subclass's area method."""
    return s.area()


def total_area(shapes: list[Shape]) -> int:
    total: int = 0
    for s in shapes:
        total = total + s.area()
    return total


def main() -> None:
    r: Rectangle = Rectangle(x=0, y=0, width=5, height=3)
    c: Circle = Circle(x=1, y=1, radius=4)

    # isinstance checks with inheritance
    assert isinstance(r, Shape) == True      # Rectangle IS a Shape
    assert isinstance(c, Shape) == True      # Circle IS a Shape
    assert isinstance(r, Rectangle) == True

    # Method dispatch — must call subclass method
    assert r.area() == 15
    assert c.area() == 48

    # Through parent-typed variable
    s: Shape = r  # static type Shape, runtime type Rectangle
    assert s.area() == 15  # must dispatch to Rectangle.area
    assert s.describe() == "rectangle"

    # Polymorphic collection
    shapes: list[Shape] = [r, c]
    assert total_area(shapes) == 63  # 15 + 48

    print(r.area(), c.area(), total_area(shapes))


main()
