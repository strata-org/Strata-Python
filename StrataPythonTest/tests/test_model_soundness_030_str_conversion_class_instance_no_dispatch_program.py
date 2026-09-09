# `str(obj)` on class instances doesn't dispatch to user-defined `__str__` —
# tag-based dispatch has no slot lookup
"""
The subset says __str__ and __repr__ are IN. str(obj) should call
obj.__str__(). But the model dispatches operators by tag pattern matching
on the Any datatype — there is no slot lookup. PStr(from_ClassInstance(...))
likely returns a generic string or Hole, not the result of __str__.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int

    def __str__(self: "Point") -> str:
        return "(" + str(self.x) + ", " + str(self.y) + ")"


def format_point(p: Point) -> str:
    return str(p)


def log_message(label: str, p: Point) -> str:
    return label + ": " + str(p)


def main() -> None:
    pt: Point = Point(x=3, y=4)

    # str(pt) should call Point.__str__
    s: str = format_point(pt)
    assert s == "(3, 4)"

    msg: str = log_message("position", pt)
    assert msg == "position: (3, 4)"

    print(s)
    print(msg)


main()
