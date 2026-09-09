# @dataclass inheritance positional arg ordering — child constructor takes
# parent fields first (MRO order); translator may misordering positional args
"""
DATACLASS INHERITANCE CONSTRUCTOR FIELD ORDERING — CHILD POSITIONAL ARGS

The subset allows:
  - Single inheritance (IN)
  - @dataclass (IN)
  - Dataclass inheritance (IN, finding 143)

The NOVEL gap: when a child @dataclass inherits from a parent @dataclass,
CPython's generated __init__ takes PARENT fields first, then CHILD fields,
in declaration order. The model must maintain this ordering for positional
construction to work correctly.

  @dataclass
  class Animal:
      name: str
      age: int

  @dataclass
  class Dog(Animal):
      breed: str

  Dog("Rex", 5, "Labrador")
  # CPython: name="Rex", age=5, breed="Labrador"
  # Model may: breed="Rex", name=5, age="Labrador" (wrong field mapping)
  #        or: name="Rex", breed=5, age="Labrador" (child fields interleaved)

Finding 143 covers the EXISTENCE of parent+child fields in the union.
Finding 230 covers field ORDER within a single class.
This finding covers the CROSS-CLASS ordering when positional args are used
at the construction site of a CHILD class.

ROOT CAUSE: The translator must know the MRO-ordered field list for each
class to correctly map positional constructor arguments. If it only sees
the child's declared fields, parent fields are either missing or misordered.

The @dataclass decorator in CPython collects fields by walking the MRO
(parent first, child last) and generates __init__ with that combined order.
The model must replicate this ordering or positional construction is wrong.
"""
from dataclasses import dataclass


@dataclass
class Vehicle:
    make: str
    year: int


@dataclass
class Car(Vehicle):
    doors: int
    color: str


@dataclass
class ElectricCar(Car):
    range_km: int


def create_car_positional() -> Car:
    """Positional construction: parent fields first, child fields second.
    
    CPython: Car("Toyota", 2020, 4, "red")
      → make="Toyota", year=2020, doors=4, color="red"
    
    Model risk: if translator sees Car's fields as [doors, color]
    and Vehicle's as [make, year], it might generate:
      → doors="Toyota", color=2020, make=4, year="red" (WRONG)
    Or if it interleaves:
      → make="Toyota", doors=2020, year=4, color="red" (WRONG)
    """
    c: Car = Car("Toyota", 2020, 4, "red")
    return c


def create_electric_positional() -> ElectricCar:
    """Three-level inheritance: grandparent, parent, child fields in order.
    
    CPython: ElectricCar("Tesla", 2023, 4, "white", 500)
      → make="Tesla", year=2023, doors=4, color="white", range_km=500
    
    Model must maintain: Vehicle fields → Car fields → ElectricCar fields
    """
    e: ElectricCar = ElectricCar("Tesla", 2023, 4, "white", 500)
    return e


def access_inherited_fields(e: ElectricCar) -> str:
    """Access fields from all levels of the hierarchy.
    
    After positional construction, each field must map to the correct
    positional argument regardless of which class declared it.
    """
    # All these must reflect the positional args correctly
    result: str = e.make + " " + str(e.year) + " " + e.color + " " + str(e.range_km)
    return result


def keyword_vs_positional_equivalence() -> bool:
    """Keyword and positional construction must produce identical results.
    
    This tests that the field ordering is consistent between the two forms.
    """
    pos: Car = Car("Honda", 2021, 4, "blue")
    kw: Car = Car(make="Honda", year=2021, doors=4, color="blue")
    return pos == kw


def child_field_after_parent_default() -> bool:
    """When parent has defaults, child fields still come after.
    
    Note: @dataclass requires that fields with defaults come after
    fields without defaults in the MRO-ordered list. This constrains
    valid inheritance patterns.
    """
    # This is a valid pattern: parent has no defaults, child has no defaults
    c: Car = Car("Ford", 2022, 2, "black")
    return c.make == "Ford" and c.doors == 2


def main() -> None:
    # Test positional construction ordering
    c: Car = create_car_positional()
    assert c.make == "Toyota"
    assert c.year == 2020
    assert c.doors == 4
    assert c.color == "red"

    # Test three-level inheritance
    e: ElectricCar = create_electric_positional()
    assert e.make == "Tesla"
    assert e.year == 2023
    assert e.doors == 4
    assert e.color == "white"
    assert e.range_km == 500

    # Test field access
    desc: str = access_inherited_fields(e)
    assert desc == "Tesla 2023 white 500"

    # Test keyword/positional equivalence
    assert keyword_vs_positional_equivalence()

    # Test parent field access
    assert child_field_after_parent_default()

    print("all passed")


main()
