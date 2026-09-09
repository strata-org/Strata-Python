# **CRITICAL**: Operator catch-all must be `exception(TypeError)` not Hole —
# Hole defeats verification; buggy code "verifies"
"""
OPERATOR CATCH-ALL MUST BE TypeError NOT Hole — SOUNDNESS CRITICAL

CPython: "hello" + 5 → TypeError (can't add str and int)
         None + 1    → TypeError
         [1,2] - [3] → TypeError

Model:   PAdd(from_str("hello"), from_int(5))
         → match: no (from_str, from_int) case
         → catch-all: return Hole (unconstrained value)

         Hole is UNSOUND because:
         1. Hole can satisfy ANY assertion (it's unconstrained)
         2. Code after the TypeError is modeled as reachable
         3. The verifier says "verified ✓" for code that CRASHES

         The catch-all MUST return exception(TypeError) because:
         1. exception tag fails return-type assertions (finding 210)
         2. Code after the error is unreachable (exception propagation)
         3. The verifier correctly reports "possible TypeError"

This is THE MOST CRITICAL soundness issue in the operator dispatch.
Hole defeats the entire purpose of verification.

Finding 204/270/286 identified this. This finding provides the
COMPREHENSIVE test showing Hole allows WRONG code to verify.
"""


def str_plus_int() -> str:
    """Should raise TypeError — model returns Hole → "verifies"."""
    result: str = "hello" + 5  # type: ignore
    # CPython: TypeError at runtime
    # Model with Hole: result is unconstrained, passes str assertion
    return result


def none_arithmetic() -> int:
    """Should raise TypeError."""
    result: int = None + 1  # type: ignore
    # CPython: TypeError
    # Model with Hole: result is unconstrained, passes int assertion
    return result


def use_after_type_error() -> int:
    """Code after TypeError should be unreachable."""
    x: int = "hello" + 5  # type: ignore  # TypeError here
    # Everything below should be unreachable
    y: int = x + 10  # operates on Hole → more Hole
    z: int = y * 2   # more Hole
    return z  # returns Hole — passes int assertion!


def conditional_type_error(flag: bool) -> int:
    """TypeError on one path — verifier must detect it."""
    if flag:
        result: int = 42
    else:
        result = "oops" + 5  # type: ignore  # TypeError
    return result


def main() -> None:
    # These should all raise TypeError in CPython
    raised1: bool = False
    try:
        str_plus_int()
    except TypeError:
        raised1 = True
    assert raised1

    raised2: bool = False
    try:
        none_arithmetic()
    except TypeError:
        raised2 = True
    assert raised2

    raised3: bool = False
    try:
        use_after_type_error()
    except TypeError:
        raised3 = True
    assert raised3

    # Conditional: only raises on False path
    assert conditional_type_error(True) == 42
    raised4: bool = False
    try:
        conditional_type_error(False)
    except TypeError:
        raised4 = True
    assert raised4

    print("all passed")


main()
