# `not` on non-bool returns bool — `not 0` → True; PNot only handles
# from_bool, returns Hole for from_int/from_str
"""
CPython: `not 0` → True (bool), `not ""` → True (bool), `not 5` → False (bool)
Model:   PNot(from_int(0)) → Hole (only handles from_bool)

Python's `not` operator:
1. Evaluates truthiness of operand (Any → bool)
2. Returns the NEGATION as a bool (always True or False)

`not x` is equivalent to `not bool(x)` — always returns a bool.

If PNot only handles from_bool, then `not 0`, `not ""`, `not []` all
return Hole instead of from_bool(True).
"""


def not_zero() -> bool:
    return not 0  # True (0 is falsy)


def not_nonzero() -> bool:
    return not 5  # False (5 is truthy)


def not_empty_string() -> bool:
    return not ""  # True ("" is falsy)


def not_nonempty_string() -> bool:
    return not "hello"  # False ("hello" is truthy)


def not_in_condition(x: int) -> str:
    """Common pattern: `if not x` where x is int."""
    if not x:  # equivalent to: if x == 0
        return "zero"
    return "nonzero"


def double_not(x: int) -> bool:
    """not not x — converts to bool."""
    return not not x  # True if x is truthy


def main() -> None:
    # CPython: not 0 = True, not 5 = False
    assert not_zero() == True
    assert not_nonzero() == False

    # CPython: not "" = True, not "hello" = False
    assert not_empty_string() == True
    assert not_nonempty_string() == False

    # In condition
    assert not_in_condition(0) == "zero"
    assert not_in_condition(42) == "nonzero"

    # Double not = truthiness conversion
    assert double_not(0) == False
    assert double_not(1) == True
    assert double_not(-5) == True

    print(not_zero(), not_nonzero(), not_in_condition(0))


main()
