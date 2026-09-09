# @dataclass equality field-by-field — must compare each field with PEq; raw
# structural equality may be order-dependent or incomplete
"""
@dataclass EQUALITY — FIELD-BY-FIELD COMPARISON

CPython: @dataclass generates __eq__ that compares ALL fields:
         Point(1, 2) == Point(1, 2) → True
         Point(1, 2) == Point(1, 3) → False (y differs)

Model:   PEq(from_ClassInstance("Point", attrs1), from_ClassInstance("Point", attrs2))
         Must compare: attrs1["x"] == attrs2["x"] AND attrs1["y"] == attrs2["y"]

         If PEq uses STRUCTURAL equality on the entire DictStrAny:
         - Order-dependent (finding 369/041)
         - May not recursively compare nested values

         If PEq just checks classname equality (without field comparison):
         - All Points are "equal" regardless of field values (WRONG)

CPython result: Point(1,2) == Point(1,3) → False
Model result: depends on PEq implementation — may be True (over-proves) or Unknown
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Color:
    r: int
    g: int
    b: int


def points_equal(a: Point, b: Point) -> bool:
    return a == b


def find_point(points: list[Point], target: Point) -> int:
    """Find index of target point using ==."""
    i: int = 0
    for p in points:
        if p == target:
            return i
        i += 1
    return -1


def remove_duplicates(points: list[Point]) -> list[Point]:
    """Remove duplicate points using ==."""
    result: list[Point] = []
    for p in points:
        found: bool = False
        for existing in result:
            if existing == p:
                found = True
                break
        if not found:
            result.append(p)
    return result


def main() -> None:
    # Test 1: same fields → equal
    assert points_equal(Point(1, 2), Point(1, 2))

    # Test 2: different fields → not equal
    assert not points_equal(Point(1, 2), Point(1, 3))
    assert not points_equal(Point(1, 2), Point(3, 2))

    # Test 3: find in list
    pts: list[Point] = [Point(0, 0), Point(1, 1), Point(2, 2)]
    assert find_point(pts, Point(1, 1)) == 1
    assert find_point(pts, Point(5, 5)) == -1

    # Test 4: deduplication
    dups: list[Point] = [Point(1, 1), Point(2, 2), Point(1, 1), Point(3, 3), Point(2, 2)]
    unique: list[Point] = remove_duplicates(dups)
    assert len(unique) == 3

    # Test 5: three-field dataclass
    c1: Color = Color(255, 0, 0)
    c2: Color = Color(255, 0, 0)
    c3: Color = Color(0, 255, 0)
    assert c1 == c2
    assert c1 != c3

    print("all passed")


main()
