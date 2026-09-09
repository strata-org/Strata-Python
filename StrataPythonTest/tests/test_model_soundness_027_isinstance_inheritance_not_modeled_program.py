# `isinstance(subclass_obj, ParentClass)` fails — model checks exact classname
# string, not inheritance hierarchy
"""
isinstance(obj, ParentClass) returns True for instances of subclasses.
The Laurel model's from_ClassInstance stores a single classname string.
isinstance likely checks classname == "ParentClass" (exact match), which
fails for Child instances where classname is "Child".
"""
from dataclasses import dataclass


@dataclass
class Animal:
    name: str


@dataclass
class Dog(Animal):
    breed: str


def is_animal(obj: Animal) -> bool:
    return isinstance(obj, Animal)


def describe(obj: Animal) -> str:
    if isinstance(obj, Dog):
        return obj.name + " the dog"
    return obj.name


def main() -> None:
    d: Dog = Dog(name="Rex", breed="Labrador")

    # isinstance checks inheritance: Dog IS an Animal
    assert is_animal(d) == True

    # isinstance narrows to subclass
    result: str = describe(d)
    assert result == "Rex the dog"

    a: Animal = Animal(name="Cat")
    assert is_animal(a) == True

    # Animal is NOT a Dog
    result2: str = describe(a)
    assert result2 == "Cat"

    print(result, result2)


main()
