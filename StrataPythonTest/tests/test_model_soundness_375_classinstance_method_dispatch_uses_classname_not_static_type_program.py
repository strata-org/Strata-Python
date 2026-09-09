# Method dispatch must use runtime classname not static type —
# `animal.speak()` on Dog must call Dog_speak; static dispatch calls
# Animal_speak (WRONG)
"""
ClassInstance METHOD DISPATCH USES classname NOT STATIC TYPE

CPython: obj.method() dispatches based on obj's RUNTIME type.
         If obj is a Dog (subclass of Animal), obj.speak() calls Dog.speak.

Model:   Method call translates to ClassName_method(obj).
         The question: which ClassName does the translator use?

         Option 1: STATIC type from annotation → Animal_speak(obj)
           WRONG if obj is actually a Dog (finding 055)

         Option 2: RUNTIME classname from the value → classname(obj)_speak(obj)
           Requires dynamic dispatch on classname string.
           Not directly expressible in Laurel (no computed function names).

         Option 3: if/elif chain on classname:
           if classname(obj) == "Dog": Dog_speak(obj)
           elif classname(obj) == "Cat": Cat_speak(obj)
           else: Animal_speak(obj)
           CORRECT but requires enumerating all subclasses.

Finding 055 identified the issue. This finding shows the CONCRETE
failure: calling a method on a parent-typed variable holding a child
instance dispatches to the WRONG method.
"""
from dataclasses import dataclass


class Animal:
    def __init__(self: "Animal", name: str) -> None:
        self.name: str = name

    def speak(self: "Animal") -> str:
        return self.name + " says nothing"

    def describe(self: "Animal") -> str:
        return "animal: " + self.name


class Dog(Animal):
    def __init__(self: "Dog", name: str) -> None:
        super().__init__(name)

    def speak(self: "Dog") -> str:
        return self.name + " says woof"


class Cat(Animal):
    def __init__(self: "Cat", name: str) -> None:
        super().__init__(name)

    def speak(self: "Cat") -> str:
        return self.name + " says meow"


def make_sound(animal: Animal) -> str:
    """Polymorphic dispatch through parent-typed parameter."""
    # CPython: dispatches to Dog.speak or Cat.speak based on runtime type
    # Model (static dispatch): always calls Animal.speak → WRONG
    return animal.speak()


def all_sounds(animals: list[Animal]) -> list[str]:
    """Dispatch in loop over heterogeneous list."""
    result: list[str] = []
    for a in animals:
        result.append(a.speak())
    return result


def main() -> None:
    d: Dog = Dog("Rex")
    c: Cat = Cat("Whiskers")

    # Test 1: direct call on child (static type matches)
    assert d.speak() == "Rex says woof"
    assert c.speak() == "Whiskers says meow"

    # Test 2: through parent-typed parameter (DISPATCH REQUIRED)
    # CPython: make_sound(d) → "Rex says woof" (Dog.speak)
    # Model (static): make_sound(d) → "Rex says nothing" (Animal.speak)
    assert make_sound(d) == "Rex says woof"
    assert make_sound(c) == "Whiskers says meow"

    # Test 3: inherited method (not overridden)
    # describe() is only on Animal — both should use it
    assert d.describe() == "animal: Rex"

    # Test 4: list of mixed types
    animals: list[Animal] = [d, c]
    sounds: list[str] = all_sounds(animals)
    assert sounds[0] == "Rex says woof"
    assert sounds[1] == "Whiskers says meow"

    print("all passed")


main()
