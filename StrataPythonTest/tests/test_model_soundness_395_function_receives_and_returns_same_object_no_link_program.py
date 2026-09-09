# Function returns input param — no link in model; SOUND because reassignment
# (not mutation) breaks alias in CPython too
"""
FUNCTION RECEIVES AND RETURNS SAME OBJECT — NO LINK IN MODEL

CPython: def identity(x): return x
         obj = Point(1, 2)
         result = identity(obj)
         result is obj → True (same object!)
         obj.x = 99 → result.x is also 99 (aliased!)

Model:   identity(x) returns a COPY of x.
         result is an independent value.
         Modifying obj doesn't affect result.

Under functional style (reassignment):
         obj = Point(99, 2)  → result is still Point(1, 2)
         CPython: result is still Point(1, 2) (obj now points elsewhere)
         BOTH AGREE — reassignment breaks the alias in CPython too.

The UNSOUND case: in-place mutation after identity return.
The SOUND case: reassignment after identity return.

The subset's functional discipline makes this safe, but the AST
checker must ensure no in-place mutation of the returned reference.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def identity(p: Point) -> Point:
    """Returns the same object (in CPython) / copy (in model)."""
    return p


def pass_through(p: Point, offset: int) -> Point:
    """Returns new object based on input — no aliasing issue."""
    return Point(p.x + offset, p.y + offset)


def store_and_retrieve(p: Point) -> Point:
    """Store in local, return — same as identity."""
    saved: Point = p
    return saved


def main() -> None:
    original: Point = Point(1, 2)

    # Test 1: identity returns "same" value
    result: Point = identity(original)
    assert result.x == 1 and result.y == 2

    # Test 2: reassign original — result unchanged (BOTH models agree)
    original = Point(99, 99)
    # CPython: result still points to old Point(1,2)
    # Model: result is independent copy of Point(1,2)
    assert result.x == 1 and result.y == 2

    # Test 3: pass_through creates genuinely new object
    p: Point = Point(5, 10)
    moved: Point = pass_through(p, 3)
    assert moved.x == 8 and moved.y == 13
    assert p.x == 5  # original unchanged

    # Test 4: store_and_retrieve
    p2: Point = Point(7, 8)
    retrieved: Point = store_and_retrieve(p2)
    p2 = Point(0, 0)  # reassign p2
    assert retrieved.x == 7  # retrieved is independent

    print("all passed")


main()
