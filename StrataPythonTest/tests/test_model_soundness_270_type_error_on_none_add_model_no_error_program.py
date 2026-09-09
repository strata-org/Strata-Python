# `None + 1`: CPython=TypeError, Model=Hole — catch-all returns Hole not
# exception; model misses type error; defeats purpose
"""
CPython: None + 1 → TypeError: unsupported operand type(s) for +: 'NoneType' and 'int'
Model:   PAdd(from_None(), from_int(1)) = Hole ← NO ERROR

The model returns Hole (unconstrained value) instead of an exception.
This means the model thinks "None + 1 might succeed" when it ALWAYS crashes.

A program that accidentally adds None to an int is "verified" by the model.
"""
from typing import Optional


def add_none_to_int() -> int:
    """CPython: TypeError. Model: Hole (no error)."""
    x: Optional[int] = None
    return x + 1  # type: ignore — TypeError at runtime!


def multiply_none() -> int:
    """CPython: TypeError. Model: Hole."""
    x: Optional[int] = None
    return x * 2  # type: ignore


def compare_none_to_int() -> bool:
    """CPython: TypeError. Model: Hole."""
    x: Optional[int] = None
    return x > 0  # type: ignore


def main() -> None:
    # All three MUST raise TypeError
    caught1: bool = False
    try:
        add_none_to_int()
    except TypeError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        multiply_none()
    except TypeError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        compare_none_to_int()
    except TypeError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
