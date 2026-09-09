# Inherited method call on child instance — child doesn't override method;
# classname-based lookup fails to find parent's definition
"""
Inherited method call on child instance — child doesn't override method;
model's classname-based method lookup fails to find parent's method.

In CPython, method resolution follows the MRO (Method Resolution Order).
When a child class doesn't override a method, calling it on a child instance
dispatches to the parent's implementation. The Laurel model translates
method calls as direct function calls keyed by the DECLARED classname of
the receiver. If the receiver is typed as the child class, the translator
looks for `ChildClass_method` — which doesn't exist because the method
is only defined on the parent.

    class Animal:
        def speak(self) -> str:
            return "..."

    class Dog(Animal):
        def fetch(self) -> str:
            return "fetching"

    d = Dog()
    d.speak()  # CPython: calls Animal.speak via MRO → "..."
               # Model: looks for Dog_speak → not found → Hole or error

This is DISTINCT from finding 055 (override not dispatched — child HAS
the method but parent's version is called). Here the child DOESN'T have
the method at all; the parent's version must be found via inheritance.

Uses ONLY confirmed-accepted constructs: class, single inheritance, method, str.
"""
from dataclasses import dataclass


@dataclass
class Vehicle:
    make: str
    year: int

    def summary(self: "Vehicle") -> str:
        return self.make + " (" + str(self.year) + ")"

    def is_vintage(self: "Vehicle") -> bool:
        return self.year < 1990

    def age(self: "Vehicle", current_year: int) -> int:
        return current_year - self.year


@dataclass
class Car(Vehicle):
    doors: int

    def door_count(self: "Car") -> str:
        return str(self.doors) + " doors"


@dataclass
class Truck(Vehicle):
    payload_kg: int

    def can_carry(self: "Truck", weight: int) -> bool:
        return weight <= self.payload_kg


def use_inherited_method() -> str:
    """Call a method defined ONLY on parent, through child instance."""
    car: Car = Car(make="Toyota", year=1985, doors=4)
    # summary() is defined on Vehicle, NOT overridden by Car
    # CPython: MRO finds Vehicle.summary → "Toyota (1985)"
    # Model: looks for Car_summary → not found → Hole
    return car.summary()


def inherited_with_computation() -> bool:
    """Inherited method that does computation."""
    car: Car = Car(make="Ford", year=1975, doors=2)
    # is_vintage() defined on Vehicle only
    # CPython: Vehicle.is_vintage(car) → 1975 < 1990 → True
    # Model: Car_is_vintage not found → Hole
    return car.is_vintage()


def inherited_with_parameter() -> int:
    """Inherited method with additional parameter."""
    truck: Truck = Truck(make="Chevy", year=2010, payload_kg=5000)
    # age() defined on Vehicle only
    # CPython: Vehicle.age(truck, 2025) → 2025 - 2010 → 15
    # Model: Truck_age not found → Hole
    return truck.age(2025)


def child_method_then_parent_method() -> str:
    """Call child-specific method, then inherited parent method."""
    car: Car = Car(make="Honda", year=2020, doors=4)
    # door_count() is on Car — works fine
    d: str = car.door_count()
    # summary() is on Vehicle — requires inheritance lookup
    s: str = car.summary()
    # CPython: "4 doors" and "Honda (2020)"
    # Model: door_count works (Car_door_count exists), summary fails
    return d + " " + s


def inherited_method_uses_self_fields() -> str:
    """Parent method accesses fields declared in parent, on child instance."""
    truck: Truck = Truck(make="RAM", year=2015, payload_kg=3000)
    # summary() accesses self.make and self.year — both from Vehicle
    # Child instance has these fields (inherited from parent)
    # CPython: "RAM (2015)"
    # Model: even if method is found, field access on child's DictStrAny
    #         must include parent fields
    return truck.summary()


def main() -> None:
    # Inherited method call
    assert use_inherited_method() == "Toyota (1985)"

    # Inherited method with computation
    assert inherited_with_computation() == True

    # Inherited method with parameter
    assert inherited_with_parameter() == 15

    # Mix of child and parent methods
    assert child_method_then_parent_method() == "4 doors Honda (2020)"

    # Parent method accessing parent-declared fields on child
    assert inherited_method_uses_self_fields() == "RAM (2015)"

    print("All inherited method tests pass")


main()
