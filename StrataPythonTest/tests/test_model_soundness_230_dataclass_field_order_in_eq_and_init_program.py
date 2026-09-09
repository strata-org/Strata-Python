# @dataclass field order — positional constructor args map to fields by
# declaration order; translator must maintain ordered field list per class
"""
@dataclass field ORDER matters for:
1. __init__ parameter order: Point(x=1, y=2) — positional args follow field order
2. __eq__ comparison: compares fields in declaration order
3. Inheritance: parent fields come before child fields

The model must preserve field order in the DictStrAny encoding.
But DictStrAny is an UNORDERED association list — it has no concept
of "first field" vs "second field."

For __eq__, order doesn't matter (all fields must match).
For __init__, order matters for POSITIONAL arguments:
  Point(1, 2) means x=1, y=2 (not y=1, x=2).

The translator must map positional args to field names by ORDER.

Uses ONLY confirmed-accepted constructs: @dataclass, int, str.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Person:
    name: str
    age: int
    score: int


def positional_construction() -> bool:
    """Positional args map to fields in declaration order."""
    p: Point = Point(3, 4)  # x=3, y=4 (not y=3, x=4)
    return p.x == 3 and p.y == 4


def keyword_construction() -> bool:
    """Keyword args are order-independent."""
    p: Point = Point(y=4, x=3)  # explicit names
    return p.x == 3 and p.y == 4


def three_fields_positional() -> bool:
    """Three positional args in order."""
    person: Person = Person("alice", 30, 100)
    return person.name == "alice" and person.age == 30 and person.score == 100


def mixed_positional_keyword() -> bool:
    """First positional, rest keyword."""
    person: Person = Person("bob", score=50, age=25)
    return person.name == "bob" and person.age == 25 and person.score == 50


@dataclass
class Child(Person):
    grade: int


def inheritance_field_order() -> bool:
    """Parent fields first, then child fields."""
    c: Child = Child("carol", 10, 95, 5)
    # Order: name, age, score (from Person), grade (from Child)
    return c.name == "carol" and c.age == 10 and c.score == 95 and c.grade == 5


def main() -> None:
    assert positional_construction() == True
    assert keyword_construction() == True
    assert three_fields_positional() == True
    assert mixed_positional_keyword() == True
    assert inheritance_field_order() == True

    print(positional_construction(), three_fields_positional(),
          inheritance_field_order())


main()
