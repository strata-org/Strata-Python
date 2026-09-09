# `len(a + b) == len(a) + len(b)` — string length after concat unprovable
# without axiom; use SMT-LIB `str.len`/`str.++` native connection
"""
After string concatenation, `len(a + b)` must equal `len(a) + len(b)`.
Finding 060 identified this axiom is missing. This finding provides
programs that DEPEND on this property for correctness.

Without the axiom, the solver can't prove bounds checks on concatenated
strings, can't verify padding functions, and can't reason about string
building in loops.

Uses ONLY confirmed-accepted constructs: str, +, len, int.
"""


def concat_length(a: str, b: str) -> int:
    result: str = a + b
    return len(result)  # must equal len(a) + len(b)


def pad_right(s: str, width: int) -> str:
    """Pad string to target width."""
    if len(s) >= width:
        return s
    padding: str = " " * (width - len(s))
    result: str = s + padding
    # len(result) == len(s) + len(padding) == len(s) + (width - len(s)) == width
    return result


def build_csv(items: list[str]) -> str:
    """Build comma-separated string."""
    if len(items) == 0:
        return ""
    result: str = items[0]
    i: int = 1
    while i < len(items):
        result = result + "," + items[i]
        # len grows each iteration
        i = i + 1
    return result


def length_preserved_after_ops() -> bool:
    """Verify length properties hold."""
    a: str = "hello"
    b: str = " world"
    c: str = a + b
    return len(c) == len(a) + len(b)  # 11 == 5 + 6


def main() -> None:
    assert concat_length("abc", "de") == 5
    assert concat_length("", "xyz") == 3
    assert concat_length("", "") == 0

    assert pad_right("hi", 5) == "hi   "
    assert len(pad_right("hi", 5)) == 5
    assert pad_right("hello", 3) == "hello"

    assert build_csv(["a", "b", "c"]) == "a,b,c"
    assert build_csv([]) == ""

    assert length_preserved_after_ops() == True

    print(concat_length("abc", "de"), len(pad_right("hi", 5)),
          length_preserved_after_ops())


main()
