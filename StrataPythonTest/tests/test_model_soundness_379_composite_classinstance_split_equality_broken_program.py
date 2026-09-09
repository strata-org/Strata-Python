# Composite/ClassInstance equality incompatible — structural (ClassInstance)
# vs reference (Composite); @dataclass needs structural, non-@dataclass needs
# reference
"""
COMPOSITE/CLASSINSTANCE SPLIT — EQUALITY BROKEN ACROSS BOUNDARY

The Any datatype has BOTH:
  from_ClassInstance(classname, attrs)  — value, structural equality
  from_Composite(ref)                  — reference, identity equality

If two objects of the SAME Python class are encoded differently
(one as ClassInstance, one as Composite), PEq cannot compare them.
PEq dispatches on tag: (from_ClassInstance, from_ClassInstance) works,
(from_Composite, from_Composite) works, but
(from_ClassInstance, from_Composite) has NO case → Hole.

In v1 (all ClassInstance), this doesn't arise. But it's a DESIGN
CONSTRAINT: the translator must ensure ALL instances of a given class
use the SAME encoding. Mixing is unsound.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def same_encoding_equality() -> bool:
    """Both as ClassInstance — structural equality works."""
    a: Point = Point(1, 2)
    b: Point = Point(1, 2)
    # Both from_ClassInstance("Point", {"x":1, "y":2})
    # PEq: structural comparison → True
    return a == b


def different_instances_not_equal() -> bool:
    """Different field values — not equal."""
    a: Point = Point(1, 2)
    b: Point = Point(3, 4)
    return a != b


def equality_after_construction() -> bool:
    """Construct same values independently — must be equal (@dataclass)."""
    p1: Point = Point(5, 10)
    p2: Point = Point(5, 10)
    # @dataclass generates __eq__ that compares fields
    # Model (ClassInstance): structural equality → True ✓
    # Model (Composite): reference equality → False ✗ (different refs!)
    return p1 == p2


def equality_in_list_search() -> bool:
    """Search by equality — requires correct == semantics."""
    points: list[Point] = [Point(1, 1), Point(2, 2), Point(3, 3)]
    target: Point = Point(2, 2)
    # target is a NEW construction — same fields as points[1]
    # ClassInstance: structural match → found ✓
    # Composite: different ref → not found ✗
    return target in points


def main() -> None:
    assert same_encoding_equality()
    assert different_instances_not_equal()
    assert equality_after_construction()
    assert equality_in_list_search()

    print("all passed")


main()
