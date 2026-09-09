# Pure @dataclass methods need no heap threading — POSITIVE: v1 ClassInstance
# encoding correctly avoids Composite complexity for functional style
"""
HEAP THREADING MISSING FOR PURE METHODS — UNNECESSARY HEAP PARAMETER

Laurel's heap parameterization pass automatically threads `heap: THeap`
through procedures that read/write fields. But for PURE methods
(functional style, return new instance, don't modify heap):

Problem 1: If the pass ADDS heap threading to pure methods,
  the method signature changes. Callers must pass/receive heap.
  But the heap is UNCHANGED — unnecessary complexity.

Problem 2: If the pass DOESN'T add heap threading,
  the method can't read fields from self (field read requires heap).
  But self is from_ClassInstance with inline attrs — no heap needed!

The v1 encoding (ClassInstance, no heap) avoids this entirely.
But it means: if ANY method in the program needs heap semantics,
ALL methods get heap threading — even pure ones.

This finding tests that pure @dataclass methods work WITHOUT
heap threading — confirming the v1 approach is correct.
"""
from dataclasses import dataclass


@dataclass
class Vector:
    x: float
    y: float

    def add(self: "Vector", other: "Vector") -> "Vector":
        """Pure method: reads fields, returns new instance. No heap needed."""
        return Vector(self.x + other.x, self.y + other.y)

    def scale(self: "Vector", factor: float) -> "Vector":
        """Pure method: no mutation."""
        return Vector(self.x * factor, self.y * factor)

    def dot(self: "Vector", other: "Vector") -> float:
        """Pure method: returns primitive, no mutation."""
        return self.x * other.x + self.y * other.y

    def length_sq(self: "Vector") -> float:
        """Pure method: reads own fields only."""
        return self.x * self.x + self.y * self.y


def vector_operations() -> float:
    """Chain of pure operations — no heap needed anywhere."""
    a: Vector = Vector(1.0, 2.0)
    b: Vector = Vector(3.0, 4.0)

    c: Vector = a.add(b)        # pure: returns new Vector
    d: Vector = c.scale(2.0)    # pure: returns new Vector
    result: float = d.dot(a)    # pure: returns float

    return result


def multiple_objects_pure() -> bool:
    """Multiple objects, all pure operations — no heap interaction."""
    v1: Vector = Vector(1.0, 0.0)
    v2: Vector = Vector(0.0, 1.0)
    v3: Vector = v1.add(v2)

    # All objects independent, all operations pure
    # No heap threading needed
    return v3.x == 1.0 and v3.y == 1.0 and v1.x == 1.0 and v2.y == 1.0


def main() -> None:
    # Test 1: chain of pure operations
    result: float = vector_operations()
    # a=(1,2), b=(3,4), c=(4,6), d=(8,12), d.dot(a) = 8*1 + 12*2 = 32
    assert result == 32.0

    # Test 2: independence preserved through pure ops
    assert multiple_objects_pure()

    # Test 3: original unchanged after pure method
    v: Vector = Vector(5.0, 10.0)
    v2: Vector = v.scale(3.0)
    assert v.x == 5.0 and v.y == 10.0  # original unchanged
    assert v2.x == 15.0 and v2.y == 30.0  # new value

    print("all passed")


main()
