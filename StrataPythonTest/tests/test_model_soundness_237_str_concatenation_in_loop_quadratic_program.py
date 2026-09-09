# String concatenation in loop — length growth requires
# len(a+b)==len(a)+len(b) axiom applied each iteration; analog of finding 233
"""
Building a string in a loop via concatenation: `result = result + s`.
Under pure string semantics, each concatenation creates a NEW string.
The model must track that `result` grows each iteration.

The key verification challenge: proving properties about the FINAL
string after the loop. E.g., len(result) == sum of len(parts).

This interacts with:
- Finding 232: len(a+b) == len(a) + len(b)
- Finding 169: while exit condition
- Finding 154: list growth in loop (analogous for strings)

Uses ONLY confirmed-accepted constructs: str, +, len, while, for.
"""


def join_with_sep(parts: list[str], sep: str) -> str:
    """Manual str.join equivalent."""
    if len(parts) == 0:
        return ""
    result: str = parts[0]
    i: int = 1
    while i < len(parts):
        result = result + sep + parts[i]
        i = i + 1
    return result


def repeat_string(s: str, n: int) -> str:
    """Manual s * n equivalent."""
    result: str = ""
    i: int = 0
    while i < n:
        result = result + s
        i = i + 1
    return result


def build_number_string(n: int) -> str:
    """Build "0,1,2,...,n-1"."""
    if n <= 0:
        return ""
    result: str = "0"
    i: int = 1
    while i < n:
        result = result + "," + str(i)
        i = i + 1
    return result


def concat_grows_length() -> bool:
    """Each concat increases length."""
    s: str = ""
    s = s + "abc"  # len = 3
    s = s + "de"   # len = 5
    s = s + "f"    # len = 6
    return len(s) == 6


def main() -> None:
    assert join_with_sep(["a", "b", "c"], ",") == "a,b,c"
    assert join_with_sep([], ",") == ""
    assert join_with_sep(["only"], ",") == "only"

    assert repeat_string("ab", 3) == "ababab"
    assert repeat_string("x", 0) == ""

    assert build_number_string(4) == "0,1,2,3"
    assert build_number_string(1) == "0"
    assert build_number_string(0) == ""

    assert concat_grows_length() == True

    print(join_with_sep(["a", "b", "c"], "-"),
          repeat_string("xy", 2), concat_grows_length())


main()
