# `int ** negative_exponent` returns float — return TYPE changes based on
# runtime exponent sign; subset declares OUT but AST checker must enforce
"""
int ** negative_exponent RETURNS FLOAT — TYPE TAG CHANGES

CPython: 2 ** -1 → 0.5 (float!)
         2 ** 3  → 8 (int)
         The return type of ** DEPENDS ON THE SIGN OF THE EXPONENT.

Model:   PPow is uninterpreted (finding 021/295) → Hole.
         But even if PPow were defined for (from_int, from_int),
         it would need to return from_float when exponent < 0.
         A single return-type rule (int**int→int) is WRONG.

The subset says: "** with negative integer exponent and integer base
is OUT in v1." But this OUT rule must be ENFORCED by the AST checker.
If the checker doesn't reject it, the program reaches the model,
which either returns Hole or returns from_int (wrong type).
"""


def power_positive(base: int, exp: int) -> int:
    """Positive exponent: int ** int → int."""
    return base ** exp


def power_negative_returns_float(base: int, exp: int) -> float:
    """Negative exponent: int ** int → float!"""
    # This is declared OUT in the subset, but if the AST checker
    # doesn't catch it, the model produces wrong results.
    return base ** exp  # type: ignore  # mypy knows this is float


def main() -> None:
    # Test 1: positive exponent (should be IN)
    assert power_positive(2, 3) == 8
    assert power_positive(3, 2) == 9
    assert power_positive(5, 0) == 1

    # Test 2: negative exponent changes return TYPE
    # CPython: 2 ** -1 = 0.5 (float)
    # Model: PPow(from_int(2), from_int(-1)) → Hole or from_int(0) (WRONG)
    result: float = 2 ** -1
    assert result == 0.5
    assert isinstance(result, float)  # NOT int!

    # Test 3: more negative exponents
    assert 4 ** -1 == 0.25
    assert 10 ** -2 == 0.01

    # Test 4: the type changes based on RUNTIME value of exponent
    # This is why it's hard to model statically:
    exp: int = -1
    val: float = 2 ** exp  # type depends on exp's sign at runtime
    assert val == 0.5

    print("all passed")


main()
