# `len("ab" * 3) == 6` unprovable — string_repeat and str_len are independent
# uninterpreted functions; no connecting axiom `len(s*n)==len(s)*n`
"""
STRING REPEAT LENGTH HAS NO AXIOM: len(s * n) != len(s) * n IN MODEL

The subset allows:
  - String repetition: str * int (IN)
  - len() on strings (IN)
  - Integer arithmetic (IN)
  - Comparison operators (IN)

The NOVEL gap: even if string_repeat and str_len are both given SOME
axioms (findings 167, 432 cover the n<=0 case; finding 075 covers
len basics), there is NO AXIOM connecting them:

  len("ab" * 3) should equal len("ab") * 3 = 6

But string_repeat and str_len are independent uninterpreted functions.
The solver has no way to derive:
  str_len(string_repeat(s, n)) == str_len(s) * n  (for n >= 1)

This blocks verification of common patterns:
  - Buffer/padding size checks: `assert len(padding) == width`
  - Protocol framing: `header = "=" * 40; assert len(header) == 40`
  - Bounds validation after string construction

This is distinct from:
  - Finding 075 (len on strings no axioms) — that's about len being
    uninterpreted in general
  - Finding 167 (string multiply boundary cases) — that's about n<=0
    producing empty string
  - Finding 232 (len after concat) — that's about len(a+b)==len(a)+len(b)
    for concatenation, not repetition
  - Finding 432 (str*0 gives empty) — that's about the zero case only
  - Finding 439 (len of concat) — same as 232, concat not repeat

The REPEAT-LENGTH connection is a separate axiom that must be stated
independently of the concat-length axiom.
"""


def padding_check() -> bool:
    """Verify that repeated string has expected length.
    
    CPython: len("=" * 40) == 40 → True
    Model: str_len(string_repeat("=", 40)) == 40 → Unknown
    
    The model cannot prove this without the axiom:
      str_len(string_repeat(s, n)) == str_len(s) * max(0, n)
    """
    separator: str = "=" * 40
    return len(separator) == 40


def indent_check(level: int) -> bool:
    """Verify indentation string length.
    
    CPython: len("  " * level) == 2 * level (for level >= 0)
    Model: Unknown — no connection between repeat and len
    """
    indent: str = "  " * level
    expected: int = 2 * level
    return len(indent) == expected


def build_and_verify(char: str, count: int) -> str:
    """Build a repeated string and verify its length.
    
    This is a common defensive pattern: construct, then assert length.
    If the axiom is missing, the assert cannot be verified.
    """
    result: str = char * count
    # CPython: always True for count >= 0 and len(char) == 1
    # Model: cannot prove — str_len(string_repeat(char, count)) is opaque
    assert len(result) == count  # UNPROVABLE in model
    return result


def repeat_then_concat_length() -> bool:
    """Combining repeat and concat — needs BOTH axioms.
    
    len(("ab" * 3) + "c") == 6 + 1 == 7
    
    Requires:
      1. len("ab" * 3) == len("ab") * 3 == 6  (repeat axiom)
      2. len(x + "c") == len(x) + len("c") == len(x) + 1  (concat axiom)
      3. Chaining: len(x + "c") == 6 + 1 == 7
    
    If either axiom is missing, the chain breaks.
    """
    repeated: str = "ab" * 3
    combined: str = repeated + "c"
    return len(combined) == 7


def safe_truncate(s: str, max_len: int) -> str:
    """Truncate string to max_len using repetition for padding.
    
    Common pattern: pad short strings, truncate long ones.
    Verification requires knowing len(s * n) to prove bounds.
    """
    if len(s) >= max_len:
        # Would need slicing (OUT) — just return original
        return s
    # Pad to exactly max_len
    padding_needed: int = max_len - len(s)
    padding: str = " " * padding_needed
    result: str = s + padding
    # CPython: len(result) == len(s) + padding_needed == max_len
    # Model: UNPROVABLE — needs both repeat-length and concat-length axioms
    assert len(result) == max_len
    return result


def main() -> None:
    assert padding_check()
    assert indent_check(0)
    assert indent_check(1)
    assert indent_check(5)

    s: str = build_and_verify("x", 10)
    assert len(s) == 10

    assert repeat_then_concat_length()

    padded: str = safe_truncate("hi", 10)
    assert len(padded) == 10

    print("all passed")


main()
