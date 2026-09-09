# `b = a` copies value not reference — modifying `a.x` after assignment leaves
# `b.x` unchanged in model
"""
`b = a` in CPython makes b reference the SAME object as a. Modifying
through a is visible through b. Under value semantics, `b = a` COPIES
the value — a and b are independent. This is the most fundamental
consequence of "no aliasing."

The subset says aliasing is OUT for lists. But for class instances,
the subset allows `b = a` (simple assignment). The model must either:
1. Reject `b = a` for class instances (like lists)
2. Accept that modifications through a are invisible through b
"""
from dataclasses import dataclass


@dataclass
class Pair:
    x: int
    y: int


def copy_and_modify() -> bool:
    """After b = a, modifying a doesn't affect b."""
    a: Pair = Pair(x=1, y=2)
    b: Pair = a  # CPython: b IS a (same object)
    a.x = 99     # CPython: b.x is also 99
    # Value model: b.x is still 1 (independent copy)
    return b.x == 1  # Model: True. CPython: False


def swap_references() -> int:
    """Reassigning a doesn't affect b (both models agree here)."""
    a: Pair = Pair(x=1, y=2)
    b: Pair = a
    a = Pair(x=99, y=99)  # rebind a to new object
    # Both models: b still has x=1, y=2 (rebinding != mutation)
    return b.x


def pass_and_check(p: Pair) -> int:
    """Function receives a copy (value) or reference (CPython)."""
    p.x = 999
    return p.x


def main() -> None:
    # The fundamental divergence
    a: Pair = Pair(x=1, y=2)
    b: Pair = a
    a.x = 99

    # CPython: b.x == 99 (same object)
    # Model: b.x == 1 (independent copy)
    assert b.x == 99  # This is what CPython does

    # Reassignment (not mutation): both agree
    assert swap_references() == 1

    # Pass to function: CPython mutates original
    p: Pair = Pair(x=5, y=10)
    pass_and_check(p)
    # CPython: p.x == 999 (mutated through reference)
    # Model: p.x == 5 (function got a copy)
    assert p.x == 999

    print(b.x, swap_references(), p.x)


main()
