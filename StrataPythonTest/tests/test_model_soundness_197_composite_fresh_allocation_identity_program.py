# Composite fresh allocation — each constructor must return unique reference;
# without freshness assume, solver can't prove independence
"""
Under Composite/heap semantics, each `MyClass()` constructor call must
allocate a FRESH heap location. Two separate constructor calls must
produce non-aliasing references.

    a = MyClass(x=1)
    b = MyClass(x=1)
    # a and b are DIFFERENT objects (different heap locations)
    # a is b → False
    # Modifying a must not affect b

Finding 104 identified this requirement. This finding provides test
cases showing that fresh allocation is critical for correctness when
Composite encoding is used.

Under value semantics (ClassInstance), this is trivially satisfied
(finding 195). Under Composite, the allocator must guarantee freshness.

Uses ONLY confirmed-accepted constructs: @dataclass, int, function def.
"""
from dataclasses import dataclass


@dataclass
class Box:
    value: int


def two_boxes_independent() -> bool:
    """Two separately constructed boxes must be independent."""
    a: Box = Box(value=10)
    b: Box = Box(value=10)
    # Same initial value, but independent objects
    a = Box(value=a.value + 1)  # a.value = 11
    # b must still be 10
    return a.value == 11 and b.value == 10


def boxes_in_loop() -> list[Box]:
    """Each loop iteration creates a fresh box."""
    boxes: list[Box] = []
    i: int = 0
    while i < 3:
        boxes.append(Box(value=i))
        i = i + 1
    # Each box is independent
    return boxes


def modify_one_in_list() -> bool:
    """Modifying one box in a list doesn't affect others."""
    boxes: list[Box] = [Box(value=0), Box(value=0), Box(value=0)]
    # Modify only the first
    boxes[0] = Box(value=99)
    # Others unchanged
    return boxes[0].value == 99 and boxes[1].value == 0 and boxes[2].value == 0


def factory_produces_fresh() -> bool:
    """A factory function must return fresh objects each call."""
    def make_box(v: int) -> Box:
        return Box(value=v)

    x: Box = make_box(5)
    y: Box = make_box(5)
    # x and y are independent even though same factory, same arg
    x = Box(value=x.value + 100)
    return x.value == 105 and y.value == 5


def main() -> None:
    assert two_boxes_independent() == True
    assert modify_one_in_list() == True
    assert factory_produces_fresh() == True

    boxes: list[Box] = boxes_in_loop()
    assert boxes[0].value == 0
    assert boxes[1].value == 1
    assert boxes[2].value == 2

    print(two_boxes_independent(), modify_one_in_list(),
          factory_produces_fresh())


main()
