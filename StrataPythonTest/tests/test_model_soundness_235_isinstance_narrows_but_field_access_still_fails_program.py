# isinstance narrows but field access fails — narrowing gives classname but
# not field schema; need axiom: `classname=="Car" ⟹ has "doors"`
"""
After `isinstance(x, Dog)` narrows x to Dog, the model must allow
access to Dog-specific fields (like `breed`). But `from_ClassInstance`
stores ALL fields in one DictStrAny — the narrowing must tell the
solver that `breed` EXISTS in the attrs dict.

Finding 064 identified this. This finding shows the COMPLETE pattern:
isinstance narrows → field access must succeed → requires postcondition
that subclass fields are present.

Uses ONLY confirmed-accepted constructs: @dataclass, isinstance, str, int.
"""
from dataclasses import dataclass


@dataclass
class Vehicle:
    make: str
    year: int


@dataclass
class Car(Vehicle):
    doors: int


@dataclass
class Truck(Vehicle):
    payload: int


def get_doors(v: Vehicle) -> int:
    """After isinstance narrowing, access Car-specific field."""
    if isinstance(v, Car):
        return v.doors  # must be accessible after narrowing
    return 0


def get_payload(v: Vehicle) -> int:
    if isinstance(v, Truck):
        return v.payload
    return 0


def describe(v: Vehicle) -> str:
    if isinstance(v, Car):
        if v.doors == 2:
            return "coupe"
        return "sedan"
    if isinstance(v, Truck):
        if v.payload > 1000:
            return "heavy truck"
        return "light truck"
    return "vehicle"


def process_fleet(vehicles: list[Vehicle]) -> int:
    """Sum doors of cars + payload of trucks."""
    total: int = 0
    for v in vehicles:
        if isinstance(v, Car):
            total = total + v.doors
        if isinstance(v, Truck):
            total = total + v.payload
    return total


def main() -> None:
    car: Car = Car(make="Toyota", year=2020, doors=4)
    truck: Truck = Truck(make="Ford", year=2019, payload=2000)

    assert get_doors(car) == 4
    assert get_doors(truck) == 0
    assert get_payload(truck) == 2000
    assert get_payload(car) == 0

    assert describe(car) == "sedan"
    assert describe(truck) == "heavy truck"

    fleet: list[Vehicle] = [car, truck, Car(make="Honda", year=2021, doors=2)]
    assert process_fleet(fleet) == 2006  # 4 + 2000 + 2

    print(get_doors(car), describe(truck), process_fleet(fleet))


main()
