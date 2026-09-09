# Composite field holding another Composite — nested access `p.address.city`
# requires double heap dereference
"""
If user classes use Composite (heap semantics), their fields are stored
in the heap as typed values (Box: BoxInt, BoxBool, BoxFloat64, BoxComposite).
But Python fields can hold ANY type — a field declared `x: int` holds an
int, but the heap model's Box type must match.

The issue: Composite fields use Box (fixed type per field), but Python's
dynamic nature means a field could theoretically hold any type. The
translator must ensure field types are enforced at write time, and that
reads produce the correct type tag.

Additionally, if a field holds another object (BoxComposite), nested
field access requires dereferencing through the heap twice.
"""
from dataclasses import dataclass


@dataclass
class Address:
    street: str
    city: str


@dataclass
class Person:
    name: str
    age: int
    address: Address  # field holds another Composite object


def get_city(p: Person) -> str:
    # Nested access: p.address.city
    # Heap: read p.address → BoxComposite(addr_ref)
    #        read addr_ref.city → BoxString("NYC")
    return p.address.city


def update_city(p: Person, new_city: str) -> None:
    # Nested write: p.address.city = new_city
    # Must dereference p.address to get the Address ref, then write city
    p.address.city = new_city


def same_address(p1: Person, p2: Person) -> bool:
    return p1.address.city == p2.address.city


def main() -> None:
    addr: Address = Address(street="123 Main", city="NYC")
    person: Person = Person(name="Alice", age=30, address=addr)

    # Nested read
    assert get_city(person) == "NYC"

    # Nested write
    update_city(person, "LA")
    assert person.address.city == "LA"

    # The Address object was modified (heap semantics)
    # In CPython: addr.city is also "LA" (same object)
    assert addr.city == "LA"

    # Two persons with different addresses
    addr2: Address = Address(street="456 Oak", city="SF")
    person2: Person = Person(name="Bob", age=25, address=addr2)
    assert same_address(person, person2) == False

    print(get_city(person), addr.city, person2.address.city)


main()
