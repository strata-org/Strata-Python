# `len("hello" + " world")` → `11`; str_len and str_concat both uninterpreted
# → Hole; must use SMT-LIB String theory
"""
STRING LEN AFTER CONCAT — len(a + b) == len(a) + len(b)

DIVERGENCE:
  CPython:  len("hello" + " world") → 11 (5 + 6)
  Model:    str_len(str_concat("hello", " world")) → Hole (uninterpreted)

  CPython:  len("") → 0
  Model:    str_len("") → Hole (no axiom: len("") == 0)

  CPython:  len("abc") → 3
  Model:    str_len("abc") → Hole (no axiom for literals)

Without SMT-LIB String theory, ALL string length operations are
unprovable. This blocks bounds checking on string operations.
"""


def concat_len(a: str, b: str) -> int:
    """len(a + b) should equal len(a) + len(b)."""
    return len(a + b)


def is_empty(s: str) -> bool:
    """len(s) == 0 checks emptiness."""
    return len(s) == 0


def truncate(s: str, max_len: int) -> str:
    """Truncate string if too long — needs len comparison."""
    if len(s) <= max_len:
        return s
    return s  # simplified — real truncation needs slicing


def pad_check(s: str, width: int) -> bool:
    """Check if string needs padding."""
    return len(s) < width


def main() -> None:
    # CPython: len("hello" + " world") = 11
    # Model: Hole (str_len and str_concat both uninterpreted)
    assert concat_len("hello", " world") == 11

    # CPython: len("") = 0
    # Model: Hole
    assert is_empty("")
    assert not is_empty("x")

    # CPython: len("abc") = 3
    # Model: Hole
    assert len("abc") == 3
    assert len("") == 0

    # Length after concat
    a: str = "foo"
    b: str = "bar"
    assert len(a + b) == len(a) + len(b)  # 6 == 3 + 3

    # Pad check
    assert pad_check("hi", 5)
    assert not pad_check("hello", 3)

    print("all passed")


main()
