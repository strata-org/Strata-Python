# Nested field write requires chain rebuild — `obj.a.b = v` needs bottom-up
# reconstruction of entire object chain; N levels = N rebuilds
"""
"No mutation in place" means nested field writes require CHAIN REBUILDING.

    obj.inner.field = value

In CPython: modifies inner object in place (one step).
In model: requires rebuilding inner, then rebuilding outer:
    1. new_inner = reconstruct(obj.inner, field, value)
    2. new_obj = reconstruct(obj, "inner", new_inner)
    3. obj = new_obj

For deeply nested access: obj.a.b.c = v requires rebuilding c, b, a, obj.
Each level must be reconstructed with the updated child.

Finding 033 identified nested composition. Finding 107 identified
Composite nested access. This finding shows the COMPLETE chain-rebuild
pattern for value semantics.

Uses ONLY confirmed-accepted constructs: @dataclass, int, str.
"""
from dataclasses import dataclass


@dataclass
class Address:
    street: str
    city: str
    zip_code: int


@dataclass
class Person:
    name: str
    age: int
    address: Address


def update_city(p: Person, new_city: str) -> Person:
    """Update nested field: p.address.city = new_city."""
    # Must rebuild Address, then rebuild Person
    new_addr: Address = Address(
        street=p.address.street,
        city=new_city,
        zip_code=p.address.zip_code
    )
    return Person(name=p.name, age=p.age, address=new_addr)


def update_zip(p: Person, new_zip: int) -> Person:
    """Update p.address.zip_code."""
    new_addr: Address = Address(
        street=p.address.street,
        city=p.address.city,
        zip_code=new_zip
    )
    return Person(name=p.name, age=p.age, address=new_addr)


def update_preserves_other_fields(p: Person) -> bool:
    """Updating city must preserve street, zip, name, age."""
    updated: Person = update_city(p, "New York")
    return (updated.name == p.name and
            updated.age == p.age and
            updated.address.street == p.address.street and
            updated.address.zip_code == p.address.zip_code and
            updated.address.city == "New York")


def chain_updates(p: Person) -> Person:
    """Multiple nested updates in sequence."""
    p = update_city(p, "Boston")
    p = update_zip(p, 2101)
    p = Person(name=p.name, age=p.age + 1, address=p.address)
    return p


def main() -> None:
    addr: Address = Address(street="123 Main", city="Springfield", zip_code=62701)
    person: Person = Person(name="Alice", age=30, address=addr)

    # Update nested field
    updated: Person = update_city(person, "Chicago")
    assert updated.address.city == "Chicago"
    assert updated.address.street == "123 Main"  # preserved
    assert updated.name == "Alice"  # preserved

    # Original unchanged (value semantics)
    assert person.address.city == "Springfield"

    # Preserves other fields
    assert update_preserves_other_fields(person) == True

    # Chain updates
    chained: Person = chain_updates(person)
    assert chained.address.city == "Boston"
    assert chained.age == 31

    print(updated.address.city, person.address.city, chained.age)


main()
