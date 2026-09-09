# Composite allocation must return fresh identity — two `MyClass()` calls must
# produce non-aliasing references
"""
Each `MyClass()` constructor call must allocate a FRESH heap cell with
a unique identity. Two separate constructor calls produce distinct
objects even with identical field values. Under Composite semantics,
the allocator must return a reference that doesn't alias any existing
object.

This matters for: object identity (`is`), mutation independence, and
container storage (two objects in a list are distinct cells).
"""
from dataclasses import dataclass


@dataclass
class Box:
    value: int


def create_two_boxes() -> bool:
    """Two separate constructions produce independent objects."""
    a: Box = Box(value=42)
    b: Box = Box(value=42)
    # Same field values, but different objects
    # CPython: a is not b (different heap allocations)
    # Modifying one doesn't affect the other
    a.value = 99
    return b.value == 42  # b is independent of a


def create_in_loop(n: int) -> list[Box]:
    """Each iteration creates a fresh object."""
    boxes: list[Box] = []
    i: int = 0
    while i < n:
        boxes = boxes + [Box(value=i)]
        i = i + 1
    return boxes


def modify_one(boxes: list[Box]) -> None:
    """Modifying one box doesn't affect others."""
    boxes[0].value = 999


def main() -> None:
    # Two constructions are independent
    assert create_two_boxes() == True

    # Loop creates distinct objects
    boxes: list[Box] = create_in_loop(3)
    assert boxes[0].value == 0
    assert boxes[1].value == 1
    assert boxes[2].value == 2

    # Modify one: others unchanged
    modify_one(boxes)
    assert boxes[0].value == 999
    assert boxes[1].value == 1  # independent
    assert boxes[2].value == 2  # independent

    print(create_two_boxes(), boxes[1].value, boxes[2].value)


main()
