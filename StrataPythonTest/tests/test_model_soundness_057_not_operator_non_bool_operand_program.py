# `not` on non-bool operands (`not 0`, `not []`, `not ""`) — `PNot` only
# handles `from_bool`, falls to Hole for other tags
"""
Python's `not` operator returns the boolean inverse of the truthiness
of its operand. `not 0` is True, `not ""` is True, `not [1,2]` is False.
The result is ALWAYS a bool regardless of the operand type.

If the model's `PNot` only handles `from_bool` operands, then `not 0`,
`not ""`, `not []` fall to Hole. The subset says `not` is IN "when
operands are bool", but truthiness coercion means non-bool operands
appear in boolean contexts (e.g., `if not lst:` to check emptiness).
"""


def is_empty_list(xs: list[int]) -> bool:
    return not xs


def is_zero(n: int) -> bool:
    return not n


def is_blank(s: str) -> bool:
    return not s


def negate_bool(b: bool) -> bool:
    return not b


def main() -> None:
    # not on list: empty list is falsy
    assert is_empty_list([]) == True
    assert is_empty_list([1, 2]) == False

    # not on int: 0 is falsy
    assert is_zero(0) == True
    assert is_zero(5) == False

    # not on str: "" is falsy
    assert is_blank("") == True
    assert is_blank("hi") == False

    # not on bool: standard
    assert negate_bool(True) == False
    assert negate_bool(False) == True

    print(is_empty_list([]), is_zero(0), is_blank(""))


main()
