# `isinstance(True, int)` returns False in model —
# `isfrom_int(from_bool(True))` is false; bool⊂int not in isinstance
# translation
"""
isinstance(x, type(None)) — type(None) is NoneType, no class to match.

In CPython, `type(None)` returns `<class 'NoneType'>`. You can use it
in isinstance checks:
  isinstance(None, type(None))  → True
  isinstance(42, type(None))    → False

But the Laurel model's isinstance translation checks the `classname`
field of `from_ClassInstance`. `None` is `from_None()`, not a ClassInstance.
And `type(None)` has no representation — there's no "NoneType" string
in the model's class hierarchy.

More commonly, this appears as:
  isinstance(x, type(None))  — equivalent to `x is None`

But the model must handle it if it appears in code that passes mypy.
The subset allows isinstance for narrowing (IN), and type(None) is
a valid type argument in CPython.

Actually — checking the subset more carefully, isinstance is IN for
T ∈ {int, float, str, bool, list, dict, tuple, <user class>}.
`type(None)` is NOT in this list. So this may already be OUT.

But `isinstance(x, int)` where x is `from_bool(True)` has the SAME
issue: CPython returns True (bool⊂int), model checks tag and returns
False (from_bool ≠ from_int).

This finding focuses on isinstance with bool/int subtyping.

Uses ONLY confirmed-accepted constructs: isinstance, bool, int, if.
"""


def isinstance_bool_is_int(x: bool) -> bool:
    """isinstance(True, int) is True in CPython."""
    return isinstance(x, int)
    # CPython: True (bool is subclass of int)
    # Model: checks isfrom_int(from_bool(True)) → False — WRONG


def isinstance_narrows_bool_to_int(x: object) -> int:
    """After isinstance(x, int), x could be bool OR int."""
    if isinstance(x, int):
        # CPython: reaches here for both int AND bool values
        return x + 1  # type: ignore
    return 0
    # Model: isinstance checks isfrom_int only
    #   from_bool(True) fails the check → takes else branch → returns 0
    #   CPython: True passes → returns True + 1 = 2


def filter_ints_includes_bools(xs: list[object]) -> list[int]:
    """Filtering by isinstance(x, int) should include bools."""
    result: list[int] = []
    for x in xs:
        if isinstance(x, int):  # type: ignore
            result.append(x)  # type: ignore
    return result
    # CPython with [1, True, "a", False, 2]:
    #   result = [1, True, False, 2] (bools pass isinstance int check)
    # Model: only [1, 2] (from_bool values fail isfrom_int check)


def isinstance_none_check() -> bool:
    """isinstance(None, type(None)) — if type(None) were allowed."""
    # This is equivalent to `x is None` but uses isinstance
    # The subset may not allow type(None) as isinstance argument
    # But the bool⊂int case IS in the subset
    x: int = True  # type: ignore  # valid: bool is int
    return isinstance(x, int)
    # CPython: True
    # Model: x is from_bool(True), isinstance checks isfrom_int → False


def main() -> None:
    assert isinstance_bool_is_int(True) == True
    assert isinstance_bool_is_int(False) == True
    assert isinstance_narrows_bool_to_int(True) == 2  # type: ignore
    assert isinstance_narrows_bool_to_int(42) == 43  # type: ignore
    assert isinstance_none_check() == True
