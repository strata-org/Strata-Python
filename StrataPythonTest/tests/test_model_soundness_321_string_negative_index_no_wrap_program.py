# String negative indexing `s[-1]` — no index-wrapping for strings; same gap
# as finding 020 but for `from_str`
"""
String negative indexing s[-1] — no index-wrapping for strings.

Finding 020 covers negative list indexing (List_get has no wrap logic).
This finding covers the SAME gap for strings: s[-1] should return the
last character, but the model's string subscript (finding 069) has no
negative-index wrapping either.

In CPython:
  s = "hello"
  s[-1]  → "o"  (wraps to s[len(s)-1] = s[4])
  s[-2]  → "l"  (wraps to s[3])
  s[-5]  → "h"  (wraps to s[0])
  s[-6]  → IndexError (out of bounds)

The model's str_char_at (if it exists per finding 069) likely takes
the index as-is. Negative indices either:
  - Return Hole (index not found in string)
  - Map to some undefined position
  - Produce exception(IndexError) unconditionally

Uses ONLY confirmed-accepted constructs: str, int, subscript, len.
"""


def last_char(s: str) -> str:
    """s[-1] returns last character."""
    return s[-1]
    # CPython: "hello"[-1] → "o"
    # Model: str_char_at("hello", -1) → Hole or wrong char


def second_to_last(s: str) -> str:
    """s[-2] returns second-to-last."""
    return s[-2]
    # CPython: "hello"[-2] → "l"
    # Model: Hole


def negative_index_equivalence(s: str, i: int) -> bool:
    """s[-i] == s[len(s)-i] for valid negative indices."""
    if i > 0 and i <= len(s):
        return s[-i] == s[len(s) - i]
    return True
    # CPython: always True for valid i
    # Model: s[-i] is Hole, comparison unprovable


def first_via_negative(s: str) -> str:
    """s[-len(s)] returns first character."""
    n: int = len(s)
    return s[-n]
    # CPython: "hello"[-5] → "h"
    # Model: Hole


def main() -> None:
    assert last_char("hello") == "o"
    assert second_to_last("hello") == "l"
    assert negative_index_equivalence("hello", 1) == True
    assert negative_index_equivalence("hello", 3) == True
    assert first_via_negative("hello") == "h"
