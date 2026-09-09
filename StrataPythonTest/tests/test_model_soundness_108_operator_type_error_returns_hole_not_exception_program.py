# Operator type error returns Hole not exception — `"hello" + 5` silently
# produces garbage instead of TypeError
"""
When an operator is applied to incompatible types (e.g., str + int),
CPython raises TypeError. The model's tag-based dispatch falls to a
default case that returns Hole (unconstrained value) instead of
exception(TypeError). This means type errors are SILENT in the model —
the program continues with garbage instead of crashing.

The verifier should report "possible TypeError" but if the default
case is Hole, it can't distinguish "type error" from "unknown result."
"""


def add_str_int(s: str, n: int) -> str:
    # CPython: TypeError: can only concatenate str (not "int") to str
    return s + n  # type: ignore


def subtract_str(a: str, b: str) -> str:
    # CPython: TypeError: unsupported operand type(s) for -: 'str' and 'str'
    return a - b  # type: ignore


def multiply_str_str(a: str, b: str) -> str:
    # CPython: TypeError: can't multiply sequence by non-int of type 'str'
    return a * b  # type: ignore


def divide_str(a: str, b: int) -> str:
    # CPython: TypeError: unsupported operand type(s) for /: 'str' and 'int'
    return a / b  # type: ignore


def main() -> None:
    # All of these should raise TypeError
    raised1: bool = False
    try:
        x: str = add_str_int("hello", 5)
    except TypeError:
        raised1 = True
    assert raised1 == True

    raised2: bool = False
    try:
        y: str = subtract_str("a", "b")
    except TypeError:
        raised2 = True
    assert raised2 == True

    raised3: bool = False
    try:
        z: str = multiply_str_str("a", "b")
    except TypeError:
        raised3 = True
    assert raised3 == True

    raised4: bool = False
    try:
        w: str = divide_str("hello", 2)
    except TypeError:
        raised4 = True
    assert raised4 == True

    print(raised1, raised2, raised3, raised4)


main()
