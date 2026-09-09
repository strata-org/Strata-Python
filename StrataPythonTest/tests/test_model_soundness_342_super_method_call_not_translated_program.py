# `super().method()` in overriding method — super() has no representation;
# parent method logic entirely lost
"""
super().method() CALL IN OVERRIDING METHOD — NOT TRANSLATED

CPython: super().method() resolves to the parent class's method via MRO.
         The child can extend behavior by calling super() then adding logic.

Model:   super() has no representation. It's not a ClassInstance, not a
         builtin, not a function. The translator likely:
         - Drops the call entirely (silent no-op)
         - Or fails to resolve which function to call

Finding 008 covers super().__init__() specifically for field initialization.
This finding covers super().arbitrary_method() in overriding methods —
the parent's logic is LOST, only the child's additions execute.
"""


class Animal:
    def __init__(self: "Animal", name: str, legs: int) -> None:
        self.name: str = name
        self.legs: int = legs

    def describe(self: "Animal") -> str:
        return self.name + " has " + str(self.legs) + " legs"

    def can_swim(self: "Animal") -> bool:
        return False


class Dog(Animal):
    def __init__(self: "Dog", name: str, breed: str) -> None:
        super().__init__(name, 4)
        self.breed: str = breed

    def describe(self: "Dog") -> str:
        # Calls parent's describe() then extends
        base: str = super().describe()
        return base + " (" + self.breed + ")"

    def can_swim(self: "Dog") -> bool:
        # Overrides completely (no super call) — this works fine
        return True


class GuideDog(Dog):
    def __init__(self: "GuideDog", name: str, breed: str, handler: str) -> None:
        super().__init__(name, breed)
        self.handler: str = handler

    def describe(self: "GuideDog") -> str:
        # Two levels of super: GuideDog → Dog → Animal
        base: str = super().describe()
        return base + ", handler: " + self.handler


def main() -> None:
    d: Dog = Dog("Rex", "Labrador")

    # Test 1: super().describe() in Dog
    desc: str = d.describe()
    # CPython: "Rex has 4 legs (Labrador)"
    # Model: super().describe() returns Hole or is dropped
    #         → result is "" + " (" + "Labrador" + ")" or just Hole
    assert desc == "Rex has 4 legs (Labrador)"

    # Test 2: two-level super chain
    g: GuideDog = GuideDog("Buddy", "Golden", "Alice")
    gdesc: str = g.describe()
    # CPython: "Buddy has 4 legs (Golden), handler: Alice"
    # Model: entire super chain is broken
    assert gdesc == "Buddy has 4 legs (Golden), handler: Alice"

    # Test 3: super().__init__ sets parent fields
    assert d.name == "Rex"
    assert d.legs == 4
    assert d.breed == "Labrador"

    print(desc)
    print(gdesc)


main()
