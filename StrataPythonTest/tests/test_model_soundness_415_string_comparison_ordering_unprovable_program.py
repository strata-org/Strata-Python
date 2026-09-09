# `"apple" < "banana"` unprovable — str_lt uninterpreted; must map to SMT-LIB
# `str.<` for lexicographic ordering
"""
STRING COMPARISON ORDERING — UNPROVABLE WITHOUT SMT-LIB STRING THEORY

CPython: "apple" < "banana" → True (lexicographic)
         "abc" < "abd" → True
         "a" < "ab" → True (prefix is less)

Model:   PLt(from_str("apple"), from_str("banana"))
         → str_lt("apple", "banana")
         → UNPROVABLE if str_lt is uninterpreted

         SMT-LIB String theory has native `str.<` with correct
         lexicographic semantics. If mapped, these are trivially provable.

The subset declares string comparison as IN:
  "Comparison: ==, !=, <, <=, >, >= for ... str × str → bool"

But finding 047 notes str_lt may be uninterpreted.
This provides the concrete programs that fail.
"""


def is_before(a: str, b: str) -> bool:
    """Lexicographic comparison."""
    return a < b


def sort_pair(a: str, b: str) -> list[str]:
    """Sort two strings."""
    if a <= b:
        return [a, b]
    return [b, a]


def find_min_str(xs: list[str]) -> str:
    """Find lexicographically smallest string."""
    if len(xs) == 0:
        return ""
    best: str = xs[0]
    for s in xs:
        if s < best:
            best = s
    return best


def is_prefix_less(prefix: str, full: str) -> bool:
    """A proper prefix is always less than the full string."""
    # "abc" < "abcd" → True (in CPython)
    return prefix < full


def main() -> None:
    # Test 1: basic ordering
    assert is_before("apple", "banana")
    assert not is_before("banana", "apple")
    assert not is_before("same", "same")

    # Test 2: sort pair
    assert sort_pair("b", "a") == ["a", "b"]
    assert sort_pair("x", "y") == ["x", "y"]

    # Test 3: find min
    assert find_min_str(["cherry", "apple", "banana"]) == "apple"

    # Test 4: prefix ordering
    assert is_prefix_less("abc", "abcd")
    assert is_prefix_less("", "anything")

    # Test 5: character-by-character
    assert is_before("abc", "abd")  # c < d at position 2
    assert not is_before("abd", "abc")

    print("all passed")


main()
