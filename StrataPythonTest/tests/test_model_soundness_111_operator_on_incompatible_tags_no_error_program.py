# Operators on ClassInstance produce no error — `v1 + v2` on dataclass falls
# to Hole instead of TypeError
"""
Applying arithmetic operators to ClassInstance values should produce a
TypeError (no __add__/__mul__ defined — user-defined operators are OUT).
But the model's tag-based dispatch may not have a case for
from_ClassInstance, causing it to fall to Hole instead of reporting an
error. The verifier should catch this as "possible TypeError."
"""
from dataclasses import dataclass


@dataclass
class Vector:
    x: int
    y: int


def add_vectors_wrong(a: Vector, b: Vector) -> Vector:
    # This is WRONG — can't use + on dataclass instances
    # CPython: TypeError: unsupported operand type(s) for +
    return a + b  # type: ignore


def compare_vectors(a: Vector, b: Vector) -> bool:
    # < on non-comparable class: TypeError
    return a < b  # type: ignore


def main() -> None:
    v1: Vector = Vector(x=1, y=2)
    v2: Vector = Vector(x=3, y=4)

    # + on ClassInstance: TypeError
    raised1: bool = False
    try:
        v3: Vector = add_vectors_wrong(v1, v2)
    except TypeError:
        raised1 = True
    assert raised1 == True

    # < on ClassInstance: TypeError
    raised2: bool = False
    try:
        r: bool = compare_vectors(v1, v2)
    except TypeError:
        raised2 = True
    assert raised2 == True

    # - on ClassInstance: TypeError
    raised3: bool = False
    try:
        v4 = v1 - v2  # type: ignore
    except TypeError:
        raised3 = True
    assert raised3 == True

    print(raised1, raised2, raised3)


main()
