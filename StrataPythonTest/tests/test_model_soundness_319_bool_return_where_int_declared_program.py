# Function returning `bool` where `-> int` declared —
# `isfrom_int(from_bool(True))` fails; bool⊂int not in tag system
"""
Function returning bool where return type is declared int — bool⊂int.

In CPython, bool is a subclass of int. A function declared `-> int` can
legally return True or False, and the caller receives a valid int value:
  def f() -> int: return True   # valid, returns 1 (as bool, which IS int)
  x: int = f()                  # x == 1, type(x) is bool but isinstance(x, int) is True

Mypy accepts this (bool is assignable to int). CPython runs fine.

The Laurel model's return-type enforcement (finding 131) emits:
  assert isfrom_int(result)
But `True` is encoded as `from_bool(True)`, and `isfrom_int(from_bool(True))`
is FALSE. The verifier fires a spurious assertion — reporting a "possible
TypeError" for code that is perfectly valid.

This is the return-type manifestation of the bool⊂int subtyping gap
(findings 043/148/166). The model treats from_bool and from_int as
DISJOINT tags, but Python treats bool as a subtype of int.

Uses ONLY confirmed-accepted constructs: def, bool, int, return, if.
"""


def count_flags(a: bool, b: bool, c: bool) -> int:
    """Return number of True flags — result is int but computed from bools."""
    # In CPython: True + True + False = 2 (int)
    # But intermediate: True + True = 2 (int), not from_bool
    # Actually this uses arithmetic (finding 261 covers bool+bool)
    # Let's use a simpler case:
    total: int = 0
    if a:
        total = total + 1
    if b:
        total = total + 1
    if c:
        total = total + 1
    return total


def has_positive(xs: list[int]) -> int:
    """Return 1 if any positive element exists, 0 otherwise.
    
    A common pattern: return a bool from an int-declared function.
    """
    for x in xs:
        if x > 0:
            return True  # bool, but function declares -> int
    return False  # bool, but function declares -> int
    # CPython: perfectly valid. bool IS int.
    # Model: assert isfrom_int(from_bool(True)) → FAILS → spurious error


def bool_as_int_return(flag: bool) -> int:
    """Directly return a bool where int is expected."""
    return flag
    # CPython: valid. isinstance(True, int) is True.
    # Model: assert isfrom_int(from_bool(flag)) → FAILS


def conditional_bool_return(x: int) -> int:
    """Return comparison result (bool) from int function."""
    return x > 0
    # CPython: returns True or False, both valid ints
    # Model: x > 0 produces from_bool; assert isfrom_int fails


def use_bool_return() -> int:
    """Caller uses the bool-as-int return value in arithmetic."""
    a: int = has_positive([1, 2, 3])  # True (== 1)
    b: int = has_positive([-1, -2])   # False (== 0)
    return a + b
    # CPython: 1 + 0 = 1
    # Model: if has_positive returns from_bool, caller's isfrom_int check fails


def main() -> None:
    assert has_positive([1, 2, 3]) == True  # also == 1
    assert has_positive([-1, -2]) == False  # also == 0

    assert bool_as_int_return(True) == 1
    assert bool_as_int_return(False) == 0

    assert conditional_bool_return(5) == True
    assert conditional_bool_return(-3) == False

    assert use_bool_return() == 1
