# @dataclass structural equality is SOUND — model's lack of identity is
# correct for @dataclass `==`
"""
Without object identity, two independently constructed objects with the
same field values are INDISTINGUISHABLE in the model. The model treats
them as equal (structural equality). But in CPython, they're different
objects (`a is not b`).

For @dataclass (which defines __eq__), this is CORRECT — two dataclass
instances with same fields ARE equal. But for non-@dataclass classes,
this is WRONG (finding 037). This finding explores the POSITIVE case:
where lack of identity is actually sound (@dataclass equality).
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def points_equal(a: Point, b: Point) -> bool:
    return a == b


def find_point(points: list[Point], target: Point) -> int:
    """Find index of target in list using ==."""
    i: int = 0
    for p in points:
        if p == target:
            return i
        i = i + 1
    return -1


def deduplicate(points: list[Point]) -> list[Point]:
    """Remove duplicate points (by value equality)."""
    result: list[Point] = []
    for p in points:
        found: bool = False
        for r in result:
            if r == p:
                found = True
                break
        if not found:
            result = result + [p]
    return result


def main() -> None:
    # Two independent constructions with same values: equal for @dataclass
    p1: Point = Point(x=1, y=2)
    p2: Point = Point(x=1, y=2)
    assert points_equal(p1, p2) == True  # @dataclass: structural equality

    # Different values: not equal
    p3: Point = Point(x=3, y=4)
    assert points_equal(p1, p3) == False

    # Find in list
    pts: list[Point] = [Point(x=0, y=0), Point(x=1, y=2), Point(x=3, y=4)]
    assert find_point(pts, Point(x=1, y=2)) == 1
    assert find_point(pts, Point(x=5, y=5)) == -1

    # Deduplicate
    dups: list[Point] = [Point(x=1, y=1), Point(x=2, y=2), Point(x=1, y=1), Point(x=3, y=3), Point(x=2, y=2)]
    unique: list[Point] = deduplicate(dups)
    assert len(unique) == 3

    print(points_equal(p1, p2), find_point(pts, Point(x=1, y=2)), len(unique))


main()
