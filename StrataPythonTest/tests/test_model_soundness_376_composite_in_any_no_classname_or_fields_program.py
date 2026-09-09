# `from_Composite` has no classname or field schema — isinstance/dispatch
# impossible on heap-allocated objects; incompatible with ClassInstance
"""
from_Composite IN Any — NO WAY TO EXTRACT CLASSNAME OR FIELDS

The Any datatype has:
  from_Composite (as_Composite: Composite)

Where Composite is just MkComposite(ref: int) — an opaque reference.
It has NO classname, NO field schema, NO type information.

If a class instance is stored as from_Composite:
- isinstance(obj, MyClass) → can't check (no classname on Composite)
- obj.field → must go through heap: readField(heap, ref, "field")
- type(obj) → unknown (no class tag)

But from_ClassInstance has:
  from_ClassInstance (classname: string, instance_attributes: DictStrAny)

These are TWO INCOMPATIBLE representations for the same Python concept.
A program cannot use BOTH — there's no coercion between them.

If the translator puts objects in from_Composite (for heap semantics),
it loses classname (needed for isinstance/dispatch).
If it puts them in from_ClassInstance (for type info),
it loses heap semantics (needed for aliasing).
"""
from dataclasses import dataclass


@dataclass
class Animal:
    name: str
    legs: int


@dataclass
class Dog(Animal):
    breed: str


def needs_isinstance(obj: Animal) -> str:
    """Requires classname (from_ClassInstance) for isinstance."""
    if isinstance(obj, Dog):
        return "dog: " + obj.breed
    return "animal: " + obj.name


def needs_heap_semantics(animals: list[Animal]) -> None:
    """If list stores Composite refs, mutation through ref is visible.
    If list stores ClassInstance values, mutation is invisible."""
    # Under value semantics (ClassInstance): this is a copy
    # Under heap semantics (Composite): this is a reference
    pass


def needs_both(animals: list[Animal]) -> str:
    """Needs isinstance (classname) AND list storage (heap or value)."""
    for a in animals:
        if isinstance(a, Dog):
            return a.breed
    return "none"


def main() -> None:
    d: Dog = Dog("Rex", 4, "Labrador")
    a: Animal = Animal("Cat", 4)

    # Test 1: isinstance requires classname
    assert needs_isinstance(d) == "dog: Labrador"
    assert needs_isinstance(a) == "animal: Cat"

    # Test 2: list of objects with isinstance
    animals: list[Animal] = [a, d]
    assert needs_both(animals) == "Labrador"

    # Test 3: field access (works with either encoding)
    assert d.name == "Rex"
    assert d.legs == 4
    assert d.breed == "Labrador"

    print("all passed")


main()
