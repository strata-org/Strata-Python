# Subset allows isinstance + inheritance but model has no hierarchy —
# `isinstance(dog, Animal)` fails (exact string match)
"""
The subset explicitly says:
  "isinstance(x, T) for T ∈ {int, float, str, bool, list, dict, tuple,
   <user class>} — used for narrowing" is IN.
  "Single-inheritance class definitions" is IN.

But the model uses `from_ClassInstance(classname: string, ...)` with
exact string matching. `isinstance(dog, Animal)` checks
`classname == "Animal"` which fails for a Dog instance.

Finding 172 identified this. This finding shows SUBSET-PROMISED patterns
that fail: isinstance with inheritance for narrowing.

Uses ONLY confirmed-accepted constructs: class, isinstance, single inheritance.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Animal:
    name: str
    age: int


@dataclass
class Dog(Animal):
    breed: str


@dataclass
class Cat(Animal):
    indoor: bool


def is_animal(x: Animal) -> bool:
    """isinstance with parent class — subset says this is IN."""
    return isinstance(x, Animal)


def describe(a: Animal) -> str:
    """isinstance narrowing to access subclass fields."""
    if isinstance(a, Dog):
        return a.name + " (" + a.breed + ")"
    if isinstance(a, Cat):
        if a.indoor:
            return a.name + " (indoor cat)"
        return a.name + " (outdoor cat)"
    return a.name


def find_dogs(animals: list[Animal]) -> int:
    """Count dogs in a mixed list."""
    count: int = 0
    for a in animals:
        if isinstance(a, Dog):
            count = count + 1
    return count


def main() -> None:
    dog: Dog = Dog(name="Rex", age=5, breed="Lab")
    cat: Cat = Cat(name="Whiskers", age=3, indoor=True)

    # isinstance with parent class
    assert is_animal(dog) == True   # Dog IS an Animal
    assert is_animal(cat) == True   # Cat IS an Animal
    assert isinstance(dog, Dog) == True
    assert isinstance(dog, Cat) == False

    # Narrowing for field access
    assert describe(dog) == "Rex (Lab)"
    assert describe(cat) == "Whiskers (indoor cat)"

    # Mixed list
    animals: list[Animal] = [dog, cat, Dog(name="Spot", age=2, breed="Poodle")]
    assert find_dogs(animals) == 2

    print(is_animal(dog), describe(dog), find_dogs(animals))


main()
