# @dataclass equality in list `in` — `Point(2,2) in [Point(2,2)]` needs
# List_contains → PEq → deep structural ClassInstance comparison
"""
`x in lst` where lst contains @dataclass instances uses __eq__ for
comparison. @dataclass generates structural __eq__. So:

    Point(1, 2) in [Point(1, 2), Point(3, 4)]  → True

The model's PEq on ClassInstance must do STRUCTURAL comparison
(field-by-field), which matches @dataclass __eq__. Finding 121
confirmed this is correct.

But the `in` operator on lists uses List_contains, which must call
PEq on each element. If List_contains uses a DIFFERENT equality
(e.g., identity), it fails.

All constructs used: @dataclass, list, in, ==, int — all IN.
Frontend accepts this.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def point_in_list(p: Point, points: list[Point]) -> bool:
    return p in points


def find_point(points: list[Point], target: Point) -> int:
    """Find index of target point, or -1."""
    i: int = 0
    while i < len(points):
        if points[i] == target:
            return i
        i = i + 1
    return -1


def remove_duplicates(points: list[Point]) -> list[Point]:
    """Remove duplicate points (keep first occurrence)."""
    result: list[Point] = []
    for p in points:
        if p not in result:
            result.append(p)
    return result


def count_occurrences(points: list[Point], target: Point) -> int:
    count: int = 0
    for p in points:
        if p == target:
            count = count + 1
    return count


def main() -> None:
    pts: list[Point] = [Point(1, 1), Point(2, 2), Point(3, 3)]

    # Membership
    assert point_in_list(Point(2, 2), pts) == True
    assert point_in_list(Point(9, 9), pts) == False

    # Find
    assert find_point(pts, Point(2, 2)) == 1
    assert find_point(pts, Point(9, 9)) == -1

    # Dedup
    dups: list[Point] = [Point(1, 1), Point(2, 2), Point(1, 1), Point(3, 3), Point(2, 2)]
    deduped: list[Point] = remove_duplicates(dups)
    assert len(deduped) == 3

    # Count
    assert count_occurrences(dups, Point(1, 1)) == 2

    print(point_in_list(Point(2, 2), pts), find_point(pts, Point(2, 2)),
          len(deduped))


main()
