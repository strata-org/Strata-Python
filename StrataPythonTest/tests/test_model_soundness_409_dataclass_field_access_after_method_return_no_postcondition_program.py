# Dataclass method return — caller can't prove field values without inlining
# or auto-postcondition; `p.translate(1,1).x==4` unprovable
"""
DATACLASS FIELD ACCESS AFTER METHOD RETURN — NO POSTCONDITION

CPython: p = Point(3, 4); p2 = p.translate(1, 1); p2.x == 4

Model:   p.translate(1, 1) returns unconstrained value (finding 168).
         Caller has NO information about p2's fields.
         p2.x == 4 is UNPROVABLE.

         The model needs EITHER:
         - Inline the method body (bug-finding mode)
         - OR: auto-generate postcondition from method body (deductive mode)
         - OR: user-provided contract (not in subset)

Without postconditions, ANY property of a method's return value
is unprovable at the call site. This makes @dataclass methods useless
for verification — you can call them but can't reason about results.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int

    def translate(self: "Point", dx: int, dy: int) -> "Point":
        return Point(self.x + dx, self.y + dy)

    def scale(self: "Point", factor: int) -> "Point":
        return Point(self.x * factor, self.y * factor)

    def distance_sq(self: "Point") -> int:
        return self.x * self.x + self.y * self.y


def use_translate() -> bool:
    """Access fields of method return value."""
    p: Point = Point(3, 4)
    p2: Point = p.translate(1, 1)
    # CPython: p2.x == 4, p2.y == 5
    # Model without postcondition: p2 is unconstrained → unprovable
    return p2.x == 4 and p2.y == 5


def chain_methods() -> bool:
    """Chain of method calls — each return value needs postcondition."""
    p: Point = Point(1, 2)
    p = p.translate(2, 3)  # p.x==3, p.y==5
    p = p.scale(2)         # p.x==6, p.y==10
    return p.x == 6 and p.y == 10


def method_result_in_arithmetic() -> int:
    """Use method return value's field in arithmetic."""
    p: Point = Point(3, 4)
    d: int = p.distance_sq()
    # CPython: 3*3 + 4*4 = 25
    # Model: d is unconstrained (no postcondition) → can't prove d == 25
    return d


def method_result_in_condition() -> str:
    """Use method return value in condition."""
    p: Point = Point(0, 0)
    p2: Point = p.translate(5, 0)
    if p2.x > 0:
        return "moved right"
    return "stayed"


def main() -> None:
    assert use_translate()
    assert chain_methods()
    assert method_result_in_arithmetic() == 25
    assert method_result_in_condition() == "moved right"

    print("all passed")


main()
