# Subset no-aliasing rule too narrow — forbids `b = a` but not function
# parameter aliasing; `f(lst)` where f mutates lst is unsound
"""
The subset says:
  - "List append: lst.append(x)" is IN
  - "for x in lst" is IN
  - "No aliasing: assigning a list variable to another name (b = a) is OUT"

But the subset does NOT explicitly forbid:
  - Passing a list to a function (which creates a parameter alias)
  - Appending to a list parameter (mutation through alias)

The subset's "no aliasing" rule says `b = a` is OUT, but function
parameters ARE a form of aliasing: `def f(xs): xs.append(1)` creates
an alias between the caller's list and the parameter.

This is a SUBSET DEFINITION GAP: the rule is too narrow. It forbids
direct variable copy but not parameter aliasing.

Uses ONLY confirmed-accepted constructs: list, append, function def.
"""


def append_to_param(xs: list[int], val: int) -> None:
    """Appends to parameter — caller sees change in CPython."""
    xs.append(val)


def caller_sees_mutation() -> bool:
    """CPython: caller's list is modified. Model: unchanged."""
    data: list[int] = [1, 2, 3]
    append_to_param(data, 4)
    # CPython: data is [1, 2, 3, 4]
    # Model: data is [1, 2, 3] (param was a copy)
    return len(data) == 4  # True in CPython, False in model


def multiple_appends_through_param(xs: list[int]) -> None:
    """Multiple mutations through parameter."""
    xs.append(10)
    xs.append(20)
    xs.append(30)


def caller_multiple() -> int:
    data: list[int] = []
    multiple_appends_through_param(data)
    # CPython: data is [10, 20, 30], len = 3
    # Model: data is [], len = 0
    return len(data)


def correct_pattern_return(xs: list[int], val: int) -> list[int]:
    """Correct: return modified list, caller rebinds."""
    xs.append(val)
    return xs


def caller_correct() -> int:
    data: list[int] = [1, 2, 3]
    data = correct_pattern_return(data, 4)  # rebind!
    return len(data)  # 4 in both CPython and model


def main() -> None:
    # Diverging pattern
    assert caller_sees_mutation() == True  # CPython
    assert caller_multiple() == 3  # CPython

    # Correct pattern
    assert caller_correct() == 4  # Both

    print(caller_sees_mutation(), caller_multiple(), caller_correct())


main()
