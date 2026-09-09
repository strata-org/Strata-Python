# Primitives trivially correct — immutable values make aliasing unobservable;
# foundational soundness argument for int/float/str/bool/None
"""
NO ALIASING MAKES PRIMITIVES TRIVIALLY CORRECT — POSITIVE CONFIRMATION

CPython: Primitives (int, float, str, bool, None) are IMMUTABLE.
         No operation can mutate them in place.
         Therefore: aliasing is UNOBSERVABLE for primitives.
         a = 5; b = a; a += 1 → b is still 5 (in BOTH models!)

Model:   Value semantics copies the value.
         a = from_int(5); b = from_int(5); a = from_int(6)
         b is still from_int(5).

For primitives, value semantics and reference semantics are
OBSERVATIONALLY EQUIVALENT because no operation can distinguish
"same object" from "copy with same value" when the object is immutable.

This is the FOUNDATION of the model's soundness for primitive types.
"""


def int_copy_independent() -> bool:
    """Int assignment creates independent value."""
    a: int = 42
    b: int = a
    a += 1
    # CPython: b == 42 (int is immutable, += creates new int)
    # Model: b == 42 (value copy)
    return b == 42 and a == 43


def str_copy_independent() -> bool:
    """String assignment creates independent value."""
    s: str = "hello"
    t: str = s
    s = s + " world"
    # CPython: t == "hello" (str is immutable, + creates new str)
    # Model: t == "hello" (value copy)
    return t == "hello" and s == "hello world"


def float_copy_independent() -> bool:
    """Float assignment creates independent value."""
    x: float = 3.14
    y: float = x
    x = x * 2
    return y == 3.14 and abs(x - 6.28) < 0.001


def bool_copy_independent() -> bool:
    """Bool assignment creates independent value."""
    a: bool = True
    b: bool = a
    a = False
    return b and not a


def primitives_in_function(n: int) -> int:
    """Function receives primitive — caller's value unchanged."""
    n = n + 100  # reassigns LOCAL n
    return n


def main() -> None:
    assert int_copy_independent()
    assert str_copy_independent()
    assert float_copy_independent()
    assert bool_copy_independent()

    # Function doesn't affect caller's variable
    x: int = 5
    result: int = primitives_in_function(x)
    assert x == 5 and result == 105

    print("all passed")


main()
