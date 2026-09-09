# Return type enforcement — `-> int` must assert `isfrom_int(result)` at each
# return point; ensures inter-procedural soundness
"""
A function annotated `-> int` must return a value tagged `from_int`.
If the function returns a value with a different tag (e.g., from_str
or from_None), the verifier should catch this as a type error.

The model must enforce return type annotations by asserting the tag
of the return value matches the declared return type.
"""


def always_returns_int(x: int) -> int:
    return x + 1  # from_int — correct


def conditionally_typed(x: int) -> int:
    if x > 0:
        return x  # from_int — correct
    return 0      # from_int — correct


def returns_wrong_type_if_unchecked(x: int) -> int:
    # This function always returns int, but the verifier must PROVE it
    if x > 0:
        return x * 2
    if x < 0:
        return x * -1
    return 0
    # All paths return from_int — verifier should confirm


def multiple_return_paths(flag: bool, x: int, s: str) -> int:
    # All paths must return from_int
    if flag:
        return x
    return len(s)  # len returns int — correct


def main() -> None:
    assert always_returns_int(5) == 6
    assert conditionally_typed(3) == 3
    assert conditionally_typed(-1) == 0
    assert returns_wrong_type_if_unchecked(5) == 10
    assert returns_wrong_type_if_unchecked(-3) == 3
    assert returns_wrong_type_if_unchecked(0) == 0
    assert multiple_return_paths(True, 42, "hello") == 42
    assert multiple_return_paths(False, 42, "hello") == 5

    print(always_returns_int(5), conditionally_typed(-1), multiple_return_paths(False, 0, "hi"))


main()
