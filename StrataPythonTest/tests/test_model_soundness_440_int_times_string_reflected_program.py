# `3 * "ab"` → `"ababab"`; PMul has no (from_int, from_str) case → Hole; needs
# reflected dispatch or symmetric case
"""
INT * STRING — REFLECTED DISPATCH NEEDED

DIVERGENCE:
  CPython:  3 * "ab"  → "ababab" (string repeated 3 times)
  Model:    PMul(from_int(3), from_str("ab")) → Hole (no int×str case)

  CPython:  "ab" * 3  → "ababab" (same result)
  Model:    PMul(from_str("ab"), from_int(3)) → Hole (may have str×int but not int×str)

In CPython: int.__mul__(str) returns NotImplemented,
then str.__rmul__(int) is called and returns the repeated string.
The model has no reflected dispatch — only left-primary.
"""


def int_times_str(n: int, s: str) -> str:
    """int * str — needs reflected dispatch."""
    return n * s


def str_times_int(s: str, n: int) -> str:
    """str * int — may have direct case."""
    return s * n


def separator(char: str, width: int) -> str:
    """Build separator line."""
    return char * width


def indent(level: int) -> str:
    """Build indentation."""
    return level * "  "


def main() -> None:
    # CPython: 3 * "ab" = "ababab"
    # Model: PMul(from_int(3), from_str("ab")) → Hole (no case)
    assert int_times_str(3, "ab") == "ababab"

    # CPython: "ab" * 3 = "ababab"
    # Model: PMul(from_str("ab"), from_int(3)) → may work if str×int case exists
    assert str_times_int("ab", 3) == "ababab"

    # Both must give same result
    assert int_times_str(3, "x") == str_times_int("x", 3)

    # Practical uses
    assert separator("-", 5) == "-----"
    assert indent(3) == "      "  # 3 * "  " = 6 spaces

    # Edge cases
    assert int_times_str(0, "abc") == ""
    assert int_times_str(1, "abc") == "abc"

    print("all passed")


main()
