# isinstance elif exhaustive narrowing — else branch has no `assume(!cond)`
# for prior conditions; solver treats variable as unconstrained
"""
isinstance EXHAUSTIVE elif NARROWING — else branch has no negation

CPython: After `if isinstance(x, int): ... elif isinstance(x, str): ... else:`
         the else branch knows x is NEITHER int NOR str.

Model:   Each isinstance guard emits `assume(isfrom_int(x))` in its branch,
         but the final else branch has NO assumption about what x is NOT.
         The solver treats x as unconstrained in the else branch, which means
         it could be int or str — contradicting the control flow.

This causes FALSE NEGATIVES: the verifier fails to detect bugs in the else
branch because it considers impossible type combinations.
"""
from dataclasses import dataclass


class Animal:
    def __init__(self: "Animal", name: str) -> None:
        self.name: str = name


class Dog(Animal):
    def __init__(self: "Dog", name: str, breed: str) -> None:
        super().__init__(name)
        self.breed: str = breed


class Cat(Animal):
    def __init__(self: "Cat", name: str, indoor: bool) -> None:
        super().__init__(name)
        self.indoor: bool = indoor


def describe(animal: Animal) -> str:
    if isinstance(animal, Dog):
        # Branch 1: animal is Dog
        # Model: assume(classname == "Dog")
        return animal.name + " is a " + animal.breed
    elif isinstance(animal, Cat):
        # Branch 2: animal is Cat AND NOT Dog
        # Model: assume(classname == "Cat")
        # Missing: assume(classname != "Dog") — but this is implied by elif
        return animal.name + " is indoor: " + str(animal.indoor)
    else:
        # Branch 3: animal is NEITHER Dog NOR Cat
        # CPython: only reaches here if animal is plain Animal
        # Model: NO assumptions emitted — solver thinks animal could be Dog or Cat
        #        This means the verifier might not flag errors here
        return animal.name + " is unknown"


def process_value(x: int) -> str:
    """Simpler example with primitive types via Optional pattern."""
    # In a real program this would be Optional[int] narrowing
    # but the pattern is the same for isinstance chains
    if x > 0:
        return "positive"
    elif x < 0:
        return "negative"
    else:
        # CPython: x == 0 here (only possibility)
        # Model: if PLt and PGt don't emit negations in else,
        #        solver doesn't know x == 0
        assert x == 0  # Should be provable but may not be
        return "zero"


def classify_number(n: int) -> str:
    """Three-way classification where else must be exhaustive."""
    if n > 100:
        return "large"
    elif n > 10:
        # Model must know: n <= 100 AND n > 10
        # Without negation of first branch: n could be > 100 here
        return "medium"
    else:
        # Model must know: n <= 100 AND n <= 10
        # Without negations: n is unconstrained
        assert n <= 10  # Must be provable
        return "small"


def main() -> None:
    d: Dog = Dog("Rex", "Labrador")
    c: Cat = Cat("Whiskers", True)
    a: Animal = Animal("Unknown")

    assert describe(d) == "Rex is a Labrador"
    assert describe(c) == "Whiskers is indoor: True"
    assert describe(a) == "Unknown is unknown"

    assert process_value(5) == "positive"
    assert process_value(-3) == "negative"
    assert process_value(0) == "zero"

    assert classify_number(200) == "large"
    assert classify_number(50) == "medium"
    assert classify_number(5) == "small"

    print("all passed")


main()
