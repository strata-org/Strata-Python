# **ROOT CAUSE: Value semantics** — from_ClassInstance is a value; causes 26
# aliasing findings; sound IF AST check enforced
"""
ROOT CAUSE: from_ClassInstance is a VALUE, not a heap reference.
PROPERTY: No aliasing. No mutation in place. No object identity.

This single property causes findings:
001, 002, 003, 004, 005, 010, 011, 033, 048, 049, 086, 087, 094,
098, 099, 101, 118, 119, 122, 184, 192, 194, 198, 212, 215, 216.

DEMONSTRATION: Two variables pointing to "same" object are independent.
CPython: mutation through one is visible through the other.
Model: mutation through one is invisible to the other.
"""
from dataclasses import dataclass


@dataclass
class Box:
    value: int


def aliasing_divergence() -> int:
    """ROOT CAUSE DEMO: value semantics vs reference semantics."""
    a: Box = Box(value=1)
    b: Box = a  # CPython: alias. Model: copy.
    a = Box(value=99)  # CPython: a changes, b unchanged (rebind, not mutate)
    # Actually this rebinds a, so b is unchanged in BOTH.
    # The real issue is IN-PLACE mutation:
    return b.value  # 1 in both (rebind doesn't alias)


def param_aliasing() -> int:
    """The REAL divergence: function param is alias in CPython, copy in model."""
    def set_value(box: Box, v: int) -> None:
        box.value = v  # CPython: mutates caller's object. Model: mutates copy.

    b: Box = Box(value=0)
    set_value(b, 42)
    # CPython: b.value == 42 (param aliases b)
    # Model: b.value == 0 (param was a copy)
    return b.value


def list_element_aliasing() -> int:
    """Object in list aliases original in CPython."""
    b: Box = Box(value=10)
    lst: list[Box] = [b]
    b = Box(value=b.value + 90)  # rebind b to new Box(100)
    # lst[0] still has old Box(10) in BOTH (rebind, not mutate)
    return lst[0].value  # 10 in both


def main() -> None:
    assert aliasing_divergence() == 1
    # param_aliasing: CPython=42, Model=0
    val: int = param_aliasing()
    assert val == 42  # CPython behavior

    assert list_element_aliasing() == 10

    print(aliasing_divergence(), param_aliasing(), list_element_aliasing())


main()
