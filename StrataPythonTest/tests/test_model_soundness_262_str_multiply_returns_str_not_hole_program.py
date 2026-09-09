# `"ab" * 3` = "ababab" — string_repeat uninterpreted; `3 * "ha"` has no
# int×str case; both return Hole
"""
CPython results (concrete):
  "ab" * 3 = "ababab" (str)
  "x" * 0  = ""       (str)
  3 * "ha" = "hahaha" (str, reflected)

Laurel model results:
  PMul(from_str("ab"), from_int(3)) = Hole (string_repeat uninterpreted)
  PMul(from_str("x"), from_int(0))  = Hole (no zero-case axiom)
  PMul(from_int(3), from_str("ha")) = Hole (no int×str case)
"""


def str_times_int(s: str, n: int) -> str:
    return s * n


def int_times_str(n: int, s: str) -> str:
    return n * s


def main() -> None:
    # CPython: "ab" * 3 = "ababab"
    assert str_times_int("ab", 3) == "ababab"
    # CPython: "x" * 0 = ""
    assert str_times_int("x", 0) == ""
    # CPython: "hi" * 1 = "hi"
    assert str_times_int("hi", 1) == "hi"
    # CPython: "z" * -1 = ""
    assert str_times_int("z", -1) == ""

    # CPython: 3 * "ha" = "hahaha" (reflected)
    assert int_times_str(3, "ha") == "hahaha"
    assert int_times_str(0, "test") == ""

    print(str_times_int("ab", 3), str_times_int("x", 0),
          int_times_str(3, "ha"))


main()
