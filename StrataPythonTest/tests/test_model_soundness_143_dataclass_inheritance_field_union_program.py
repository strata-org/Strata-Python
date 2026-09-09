# Dataclass inheritance — subclass constructor takes parent+child fields;
# DictStrAny must contain all
"""
A @dataclass subclass inherits parent fields AND adds its own. The
constructor takes ALL fields (parent + child). The model must know
that a subclass instance has BOTH sets of fields in its DictStrAny.

@dataclass inheritance auto-generates __init__ with all fields:
parent fields first (in declaration order), then child fields.
"""
from dataclasses import dataclass


@dataclass
class Animal:
    name: str
    age: int


@dataclass
class Dog(Animal):
    breed: str


@dataclass
class ServiceDog(Dog):
    task: str


def describe_animal(a: Animal) -> str:
    return a.name + " age " + str(a.age)


def describe_dog(d: Dog) -> str:
    return d.name + " (" + d.breed + ")"


def main() -> None:
    # Dog has parent fields (name, age) + own field (breed)
    d: Dog = Dog(name="Rex", age=3, breed="Labrador")
    assert d.name == "Rex"
    assert d.age == 3
    assert d.breed == "Labrador"

    # ServiceDog has grandparent + parent + own fields
    sd: ServiceDog = ServiceDog(name="Max", age=5, breed="Shepherd", task="guide")
    assert sd.name == "Max"
    assert sd.age == 5
    assert sd.breed == "Shepherd"
    assert sd.task == "guide"

    # Access through parent type
    desc: str = describe_animal(d)
    assert desc == "Rex age 3"

    desc2: str = describe_dog(d)
    assert desc2 == "Rex (Labrador)"

    # Subclass instance passed to parent-typed function
    desc3: str = describe_animal(sd)
    assert desc3 == "Max age 5"

    print(desc, desc2, sd.task)


main()
