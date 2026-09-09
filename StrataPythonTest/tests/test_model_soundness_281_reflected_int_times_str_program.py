# Reflected dispatch: `int * str` — int.__mul__(str)→NotImplemented,
# str.__rmul__(int)→"ababab"; model has no (int,str) case → Hole
"""
MISSING REFLECTED METHOD DISPATCH: int * str

CPython protocol:
  1. int.__mul__(str) → NotImplemented
  2. str.__rmul__(int) → repeated string ✓

Model: PMul(from_int(3), from_str("ab"))
  → match: no (from_int, from_str) case
  → Hole

CPython result: "ababab"
Model result:  Hole
"""


def int_times_str(n: int, s: str) -> str:
    return n * s


def main() -> None:
    # CPython: 3 * "ab" = "ababab" (via str.__rmul__)
    assert int_times_str(3, "ab") == "ababab"
    assert int_times_str(0, "hello") == ""
    assert int_times_str(1, "x") == "x"
    assert int_times_str(-1, "y") == ""

    print(int_times_str(3, "ab"))


main()
