# `"abc" * 0` → `""`; string_repeat uninterpreted; model returns Hole instead
# of empty string for n≤0
"""
STRING MULTIPLY BY ZERO GIVES EMPTY STRING

CPython: "abc" * 0 → "" (empty string)
         "abc" * -5 → "" (negative = empty)
         "abc" * 1 → "abc"
         "abc" * 3 → "abcabcabc"

Model:   PMul(from_str("abc"), from_int(0)) → Hole (finding 015/262)
         string_repeat is uninterpreted with no axioms.
         Even if it existed: no axiom says repeat(s, 0) == ""

CPython result: ""
Model result: Hole (unconstrained — could be anything)

Root cause: string_repeat uninterpreted (finding 015).
The model doesn't know that s * 0 == "" and s * 1 == s.
"""


def repeat_zero() -> str:
    """s * 0 must be empty string."""
    return "hello" * 0


def repeat_negative() -> str:
    """s * negative must be empty string."""
    return "hello" * -5


def repeat_one() -> str:
    """s * 1 must be the string itself."""
    return "hello" * 1


def repeat_n(s: str, n: int) -> str:
    """General repetition."""
    return s * n


def pad_right(s: str, width: int) -> str:
    """Pad string to width using repetition."""
    padding: int = width - len(s)
    if padding <= 0:
        return s
    return s + " " * padding


def main() -> None:
    # Test 1: multiply by 0 → empty
    # CPython: ""
    # Model: Hole (string_repeat uninterpreted)
    assert repeat_zero() == ""

    # Test 2: multiply by negative → empty
    assert repeat_negative() == ""

    # Test 3: multiply by 1 → identity
    assert repeat_one() == "hello"

    # Test 4: general
    assert repeat_n("ab", 3) == "ababab"
    assert repeat_n("x", 5) == "xxxxx"

    # Test 5: length after repeat
    assert len("ab" * 3) == 6  # len("ab") * 3 = 2 * 3 = 6
    assert len("abc" * 0) == 0

    # Test 6: practical use — padding
    assert pad_right("hi", 5) == "hi   "
    assert pad_right("hello", 3) == "hello"  # already wide enough

    print("all passed")


main()
