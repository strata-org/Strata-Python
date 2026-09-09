# Subclass instance through parent-typed variable — classname mismatch or
# field-schema narrowing may lose subclass fields
"""
When a subclass __init__ adds fields beyond those declared in the parent,
and the object is accessed through a parent-typed variable, the model
must still have those fields available. But if the model uses the STATIC
type to determine which fields exist, accessing subclass-specific fields
through a parent-typed reference fails.

Conversely, if a parent method accesses `self.field` where `field` is
declared in the subclass, the model must find it in the DictStrAny attrs.
"""
from dataclasses import dataclass


@dataclass
class Vehicle:
    make: str
    year: int

    def summary(self: "Vehicle") -> str:
        return self.make + " " + str(self.year)


@dataclass
class Car(Vehicle):
    doors: int

    def full_summary(self: "Car") -> str:
        return self.summary() + " " + str(self.doors) + "dr"


def get_make(v: Vehicle) -> str:
    return v.make


def get_year(v: Vehicle) -> int:
    return v.year


def main() -> None:
    c: Car = Car(make="Toyota", year=2020, doors=4)

    # Access through parent-typed parameter
    m: str = get_make(c)
    assert m == "Toyota"

    y: int = get_year(c)
    assert y == 2020

    # Parent method called on subclass instance
    s: str = c.summary()
    assert s == "Toyota 2020"

    # Subclass method that calls parent method
    fs: str = c.full_summary()
    assert fs == "Toyota 2020 4dr"

    # Through a parent-typed variable
    v: Vehicle = c
    s2: str = v.summary()
    assert s2 == "Toyota 2020"

    print(m, y, s, fs)


main()
