# ClassInstance subtype at function boundary — `f(child)` where f expects
# parent; classname assertion rejects valid subclass instances
"""
ClassInstance SUBTYPE AT FUNCTION BOUNDARY — classname MISMATCH

CPython: def process(a: Animal) → str: return a.name
         process(Dog("Rex", "Lab")) → "Rex" (Dog IS-A Animal)

Model:   process expects classname == "Animal" (from parameter type)
         But receives from_ClassInstance("Dog", {...})
         classname "Dog" ≠ "Animal" → type assertion fails!

         The model's tag assertion for class-typed parameters is:
         assert isfrom_ClassInstance(a) && classname(a) == "Animal"
         This REJECTS valid subclass instances.

Finding 055 covers method dispatch (calling wrong method).
Finding 172 covers isinstance (classname has no hierarchy).
This finding covers the FUNCTION PARAMETER BOUNDARY: passing a child
instance to a function expecting the parent type.
"""
from dataclasses import dataclass


@dataclass
class Shape:
    name: str

    def area(self: "Shape") -> float:
        return 0.0


@dataclass
class Circle(Shape):
    radius: float

    def area(self: "Circle") -> float:
        return 3.14159 * self.radius * self.radius


@dataclass
class Rectangle(Shape):
    width: float
    height: float

    def area(self: "Rectangle") -> float:
        return self.width * self.height


def get_name(s: Shape) -> str:
    """Function expecting parent type — receives child instance."""
    return s.name


def total_area(shapes: list[Shape]) -> float:
    """List of parent type containing child instances."""
    total: float = 0.0
    for s in shapes:
        total += s.area()
    return total


def describe(s: Shape) -> str:
    """Access parent field on child instance through parent-typed param."""
    return s.name + " (shape)"


def main() -> None:
    c: Circle = Circle("circle", 5.0)
    r: Rectangle = Rectangle("rect", 3.0, 4.0)

    # Test 1: pass child to function expecting parent
    # CPython: works fine (Dog IS-A Animal)
    # Model: assert classname(c) == "Shape" → FAILS (classname is "Circle")
    name: str = get_name(c)
    assert name == "circle"

    # Test 2: pass different child
    name2: str = get_name(r)
    assert name2 == "rect"

    # Test 3: list of parent type with child instances
    shapes: list[Shape] = [c, r]
    # Each element has classname "Circle" or "Rectangle", not "Shape"
    # If element type assertion checks classname == "Shape" → all fail
    area: float = total_area(shapes)
    assert abs(area - (78.53975 + 12.0)) < 0.01

    # Test 4: describe through parent type
    assert describe(c) == "circle (shape)"

    print("all passed")


main()
