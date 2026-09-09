# Nested field access `person.address.city` — intermediate Any must be tag-
# checked and unwrapped at each dot; chain breaks without it
"""
NESTED DATACLASS FIELD ACCESS — p.address.city REQUIRES CHAIN

CPython: person.address.city → "NYC"
         Two-level field access: first get address, then get city.

Model:   person.address:
           DictStrAny_get(instance_attributes(person), "address")
           → returns Any (needs isfrom_ClassInstance assertion)
         Then .city:
           DictStrAny_get(instance_attributes(???), "city")
           → needs to extract instance_attributes from the intermediate result

         The intermediate result from person.address is an Any value.
         To access .city on it, the model must:
         1. Assert it's from_ClassInstance (tag check)
         2. Extract instance_attributes
         3. DictStrAny_get on those attributes

         Without step 1: accessing instance_attributes on non-ClassInstance → undefined
         Without step 2: no way to get the inner dict
         Without step 3: city value is Hole

CPython result: "NYC"
Model result: Hole (intermediate Any not unwrapped correctly)

Root cause: Nested field access requires intermediate tag assertion
and ClassInstance unwrapping at each level (finding 107).
"""
from dataclasses import dataclass


@dataclass
class Address:
    street: str
    city: str
    zip_code: str


@dataclass
class Person:
    name: str
    age: int
    address: Address


def get_city(p: Person) -> str:
    """Two-level field access."""
    return p.address.city


def get_zip(p: Person) -> str:
    """Another nested access."""
    return p.address.zip_code


def full_address(p: Person) -> str:
    """Multiple nested accesses in one function."""
    return p.address.street + ", " + p.address.city + " " + p.address.zip_code


def update_city(p: Person, new_city: str) -> Person:
    """Nested field update — requires reconstruction at both levels."""
    new_addr: Address = Address(p.address.street, new_city, p.address.zip_code)
    return Person(p.name, p.age, new_addr)


def main() -> None:
    addr: Address = Address("123 Main St", "NYC", "10001")
    person: Person = Person("Alice", 30, addr)

    # Test 1: nested field access
    assert get_city(person) == "NYC"

    # Test 2: another nested field
    assert get_zip(person) == "10001"

    # Test 3: multiple nested accesses
    assert full_address(person) == "123 Main St, NYC 10001"

    # Test 4: nested update
    moved: Person = update_city(person, "LA")
    assert moved.address.city == "LA"
    assert moved.address.street == "123 Main St"  # preserved
    assert person.address.city == "NYC"  # original unchanged

    print("all passed")


main()
