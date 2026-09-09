# String repetition boundary cases — `s * 0` and `s * (-n)` must be `""`;
# `len(s*n) == len(s)*max(0,n)` axiom needed
"""
`str * n` where n <= 0 must return the empty string "".
`str * 1` returns the original string.
`str * n` for n > 1 returns the string repeated n times.

Finding 015 identified that string_repeat is uninterpreted with no axioms.
This finding provides CONCRETE test cases showing the model diverges
for the boundary cases (n=0, n=1, n<0) and the relationship between
repetition and length: len(s * n) == len(s) * max(0, n).

Uses ONLY confirmed-accepted constructs: str, int, *, len, function def.
"""


def repeat_zero(s: str) -> str:
    return s * 0  # always ""


def repeat_negative(s: str) -> str:
    return s * -5  # always ""


def repeat_one(s: str) -> str:
    return s * 1  # same as s


def repeat_n(s: str, n: int) -> str:
    return s * n


def length_after_repeat(s: str, n: int) -> int:
    result: str = s * n
    return len(result)


def pad_to_width(s: str, width: int) -> str:
    """Pad string with spaces to reach target width."""
    padding_needed: int = width - len(s)
    if padding_needed <= 0:
        return s
    return s + " " * padding_needed


def main() -> None:
    # Zero repetition → empty
    assert repeat_zero("hello") == ""
    assert repeat_zero("") == ""
    assert len(repeat_zero("abc")) == 0

    # Negative repetition → empty
    assert repeat_negative("hello") == ""
    assert len(repeat_negative("x")) == 0

    # One repetition → identity
    assert repeat_one("hello") == "hello"
    assert repeat_one("") == ""

    # N repetitions
    assert repeat_n("ab", 3) == "ababab"
    assert repeat_n("x", 5) == "xxxxx"
    assert repeat_n("", 100) == ""

    # Length relationship: len(s * n) == len(s) * max(0, n)
    assert length_after_repeat("abc", 3) == 9   # 3 * 3
    assert length_after_repeat("abc", 0) == 0   # 3 * 0
    assert length_after_repeat("abc", -1) == 0  # 3 * max(0,-1) = 0
    assert length_after_repeat("", 5) == 0      # 0 * 5

    # Padding
    assert pad_to_width("hi", 5) == "hi   "
    assert pad_to_width("hello", 3) == "hello"  # already wider

    print(repeat_n("ab", 3), length_after_repeat("abc", 3),
          pad_to_width("hi", 5))


main()
