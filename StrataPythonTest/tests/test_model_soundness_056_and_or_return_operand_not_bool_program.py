# `and`/`or` return an operand (preserving type), not `True`/`False` — model
# may wrap result in `from_bool` losing the original type
"""
Python's `not` operator returns True or False (always a bool). But
`and` and `or` return one of their OPERANDS, not necessarily a bool:
  - `x and y` returns x if x is falsy, else y
  - `x or y` returns x if x is truthy, else y

So `0 or 5` returns 5 (an int), not True.
`"" or "default"` returns "default" (a str), not True.
`[1,2] and [3]` returns [3] (a list), not True.

If the model treats `and`/`or` as always returning from_bool, the
return type is wrong for non-bool operands.
"""


def first_truthy_int(a: int, b: int) -> int:
    return a or b


def default_string(s: str, default: str) -> str:
    return s or default


def both_positive(a: int, b: int) -> int:
    # `a and b` returns a if a is falsy (0), else b
    return a and b


def chain_or(a: int, b: int, c: int) -> int:
    return a or b or c


def main() -> None:
    # `or` returns the first truthy operand (not True/False)
    assert first_truthy_int(0, 5) == 5
    assert first_truthy_int(3, 5) == 3
    assert first_truthy_int(0, 0) == 0

    # `or` on strings
    assert default_string("", "default") == "default"
    assert default_string("hello", "default") == "hello"

    # `and` returns first falsy or last operand
    assert both_positive(3, 7) == 7
    assert both_positive(0, 7) == 0

    # chained `or`
    assert chain_or(0, 0, 9) == 9
    assert chain_or(0, 4, 9) == 4
    assert chain_or(1, 4, 9) == 1

    print(first_truthy_int(0, 5), default_string("", "default"),
          both_positive(3, 7), chain_or(0, 0, 9))


main()
