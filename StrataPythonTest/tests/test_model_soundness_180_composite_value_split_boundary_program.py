# Composite vs ClassInstance split — for v1 subset (no aliasing),
# ClassInstance is universally sound; Composite needed only if aliasing added
"""
The `Any` datatype has both `from_ClassInstance` (value semantics) and
`from_Composite` (heap semantics with modifies clauses). The question:
WHEN does a class get the Composite treatment vs ClassInstance?

If a class is encoded as ClassInstance:
- Pure value semantics, no aliasing, no mutation in place
- Methods must return new instances
- Caller must rebind after every modification

If a class is encoded as Composite:
- Heap reference semantics, aliasing possible
- Methods can modify in place (modifies clauses)
- Caller sees changes without rebinding

The PROBLEM: the translator must decide at translation time which
encoding to use. If it picks wrong:
- ClassInstance for a class that needs aliasing → unsound (findings 001-011)
- Composite for a class that's used as a value → unnecessary complexity

This finding explores the boundary: what determines which encoding a
class gets, and what happens when a class needs BOTH behaviors in
different contexts?

Uses ONLY confirmed-accepted constructs: @dataclass, class, method.
"""
from dataclasses import dataclass


@dataclass
class Point:
    """Pure value type — ClassInstance is correct."""
    x: int
    y: int

    def translate(self: "Point", dx: int, dy: int) -> "Point":
        return Point(x=self.x + dx, y=self.y + dy)

    def distance_sq(self: "Point") -> int:
        return self.x * self.x + self.y * self.y


@dataclass
class Counter:
    """Mutable state — needs rebinding under value semantics."""
    value: int

    def increment(self: "Counter") -> "Counter":
        return Counter(value=self.value + 1)

    def get(self: "Counter") -> int:
        return self.value


@dataclass
class Pair:
    """Contains two objects — demonstrates composition."""
    first: Point
    second: Point

    def translate_both(self: "Pair", dx: int, dy: int) -> "Pair":
        return Pair(
            first=self.first.translate(dx, dy),
            second=self.second.translate(dx, dy)
        )


def value_type_usage() -> int:
    """Point as pure value — ClassInstance is correct."""
    p: Point = Point(x=3, y=4)
    q: Point = p.translate(1, 1)
    # p is unchanged (value semantics — correct for immutable Point)
    # q is the new point
    return p.distance_sq() + q.distance_sq()  # 25 + 41 = 66


def counter_requires_rebinding() -> int:
    """Counter needs explicit rebinding under value semantics."""
    c: Counter = Counter(value=0)
    c = c.increment()
    c = c.increment()
    c = c.increment()
    return c.get()  # 3


def composed_objects() -> int:
    """Pair contains Points — nested value composition."""
    pair: Pair = Pair(first=Point(x=0, y=0), second=Point(x=5, y=5))
    pair = pair.translate_both(1, 1)
    return pair.first.x + pair.second.x  # 1 + 6 = 7


def main() -> None:
    assert value_type_usage() == 66  # 25 + 41
    assert counter_requires_rebinding() == 3
    assert composed_objects() == 7

    print(value_type_usage(), counter_requires_rebinding(),
          composed_objects())


main()
