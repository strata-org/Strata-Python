# `isinstance(x, (int, str))` tuple-of-types form — translator only handles
# single type; tuple form has no translation
"""
ISINSTANCE WITH TUPLE OF TYPES: isinstance(x, (int, str))

The subset allows isinstance(x, T) for narrowing. CPython also supports
isinstance(x, (T1, T2, ...)) — checking membership in a TUPLE of types.
This is IN the subset (isinstance is IN, tuples of types are standard).

CPython: isinstance(42, (int, str)) → True
Model:   isinstance translates to classname == "int" check;
         tuple-of-types form has no translation — likely Hole or always-False.

This pattern is common for handling multiple acceptable types:
    if isinstance(value, (int, float)):
        return value * 2

Root cause: isinstance translation only handles single-type second argument.
The tuple form requires OR-ing multiple tag checks.
"""


def accepts_int_or_str(x: object) -> str:
    """isinstance with tuple of types for narrowing."""
    if isinstance(x, (int, str)):
        return "accepted"
    return "rejected"


def numeric_check(x: object) -> bool:
    """Check if value is any numeric type."""
    return isinstance(x, (int, float))


def process_value(x: object) -> int:
    """Narrow with tuple, then use narrowed type."""
    if isinstance(x, (int, bool)):
        # After narrowing, x is int or bool (both support +)
        return x + 1
    return 0


def classify(x: object) -> str:
    """Multiple isinstance checks with tuple forms."""
    if isinstance(x, (int, float)):
        return "number"
    if isinstance(x, str):
        return "text"
    return "other"


def main() -> None:
    # isinstance with tuple — checks ANY of the types
    assert accepts_int_or_str(42) == "accepted"
    assert accepts_int_or_str("hello") == "accepted"
    assert accepts_int_or_str(3.14) == "rejected"

    # Numeric check
    assert numeric_check(5) == True
    assert numeric_check(3.14) == True
    assert numeric_check("5") == False

    # Narrowing after tuple isinstance
    assert process_value(10) == 11
    assert process_value(True) == 2  # True + 1 = 2
    assert process_value("x") == 0

    # Classification
    assert classify(42) == "number"
    assert classify(3.14) == "number"
    assert classify("hi") == "text"
    assert classify(None) == "other"

    print(accepts_int_or_str(42), numeric_check(5), classify(3.14))


main()
