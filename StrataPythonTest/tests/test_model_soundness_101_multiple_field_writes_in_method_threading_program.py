# Multiple field writes in method — `self.x = a; self.y = b` requires
# threading rebound self through each write
"""
When a method writes to multiple fields of self sequentially, each write
must see the effect of the previous write. Under value semantics, each
`self.field = v` creates a NEW ClassInstance. The next write must operate
on the UPDATED self, not the original.

This is the multi-statement version of finding 098. The key issue is
that the translator must THREAD the rebound self through sequential
field assignments.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int

    def move(self: "Point", dx: int, dy: int) -> "Point":
        self.x = self.x + dx  # write 1: must rebind self
        self.y = self.y + dy  # write 2: must use rebound self from write 1
        return self

    def reflect(self: "Point") -> "Point":
        old_x: int = self.x
        self.x = self.y       # write 1
        self.y = old_x        # write 2: must use self with updated x
        return self

    def scale(self: "Point", factor: int) -> "Point":
        self.x = self.x * factor  # write 1
        self.y = self.y * factor  # write 2
        return self


@dataclass
class Stats:
    total: int
    count: int
    last: int

    def record(self: "Stats", value: int) -> None:
        self.total = self.total + value  # write 1
        self.count = self.count + 1      # write 2
        self.last = value                # write 3
        # All three writes must be visible in final self


def main() -> None:
    # Move: two field writes
    p: Point = Point(x=1, y=2)
    p2: Point = p.move(3, 4)
    assert p2.x == 4  # 1 + 3
    assert p2.y == 6  # 2 + 4

    # Reflect: swap x and y
    p3: Point = Point(x=10, y=20)
    p4: Point = p3.reflect()
    assert p4.x == 20
    assert p4.y == 10

    # Scale: both fields multiplied
    p5: Point = Point(x=3, y=4)
    p6: Point = p5.scale(2)
    assert p6.x == 6
    assert p6.y == 8

    # Stats: three field writes
    s: Stats = Stats(total=0, count=0, last=0)
    s.record(10)
    # CPython: s.total=10, s.count=1, s.last=10
    # Model (no threading): each write operates on original self
    #   write 1: total=10 (on original)
    #   write 2: count=1 (on original, not on self-with-total=10)
    #   write 3: last=10 (on original)
    #   Final self has only the LAST write visible
    assert s.total == 10
    assert s.count == 1
    assert s.last == 10

    print(p2.x, p2.y, p6.x, p6.y)


main()
