# ClassInstance field write frame axiom — `obj.x = 5` must preserve `obj.y`;
# requires dict frame axiom on instance_attributes
"""
ClassInstance FIELD WRITE FRAME AXIOM — WRITING obj.x MUST PRESERVE obj.y

CPython: obj.x = 99; obj.y still has its old value.

Model:   obj.x = 99 translates to:
           attrs' = DictStrAny_set(instance_attributes(obj), "x", 99)
           obj' = from_ClassInstance(classname(obj), attrs')

         Then obj'.y = DictStrAny_get(attrs', "y")
         This requires the DICT FRAME AXIOM (finding 366):
           get(set(attrs, "x", 99), "y") == get(attrs, "y")

         Without the frame axiom, writing obj.x destroys knowledge of obj.y.

This is finding 366 (dict frame) applied specifically to ClassInstance
field access. It's the most common manifestation because every field
write on an object goes through the instance_attributes DictStrAny.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int

    def move_x(self: "Point", dx: int) -> "Point":
        return Point(self.x + dx, self.y)

    def move_y(self: "Point", dy: int) -> "Point":
        return Point(self.x, self.y + dy)


@dataclass
class Person:
    name: str
    age: int
    city: str


def write_x_preserves_y() -> bool:
    """Writing x must not affect y."""
    p: Point = Point(1, 2)
    p2: Point = Point(99, p.y)  # "write" x by reconstruction
    # p2.y must still be 2
    # Model: DictStrAny_get(set(attrs, "x", 99), "y") == ???
    # Without frame axiom: unconstrained
    return p2.y == 2


def sequential_field_writes() -> Point:
    """Multiple field writes, each preserving others."""
    p: Point = Point(0, 0)
    p = Point(10, p.y)   # write x, preserve y
    p = Point(p.x, 20)   # write y, preserve x
    # After both: x==10, y==20
    # Requires frame axiom applied at each step
    return p


def method_preserves_other_field() -> bool:
    """Method modifies one field, other preserved."""
    p: Point = Point(5, 10)
    p2: Point = p.move_x(3)
    # p2.x == 8, p2.y == 10 (preserved)
    return p2.x == 8 and p2.y == 10


def three_field_object() -> bool:
    """Three fields — writing one preserves the other two."""
    person: Person = Person("Alice", 30, "NYC")
    person2: Person = Person(person.name, 31, person.city)  # update age
    # name and city must be preserved
    return person2.name == "Alice" and person2.age == 31 and person2.city == "NYC"


def main() -> None:
    assert write_x_preserves_y()

    p: Point = sequential_field_writes()
    assert p.x == 10 and p.y == 20

    assert method_preserves_other_field()
    assert three_field_object()

    print("all passed")


main()
