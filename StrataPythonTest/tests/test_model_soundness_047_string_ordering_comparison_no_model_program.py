# String ordering comparisons (`<`, `>`, `<=`, `>=`) — `str_lt` may be
# uninterpreted with no axioms; string ordering is unprovable
"""
String ordering comparisons (`<`, `>`, `<=`, `>=`) use lexicographic
ordering based on Unicode code points. The model's PLt/PGt for strings
may use SMT string ordering (which in SMT-LIB is also lexicographic),
but if the string sort is uninterpreted or if PLt has no `str × str`
case, the result is Hole. Even if SMT string ordering is used, there
are edge cases: empty string ordering, prefix ordering, and the fact
that Python compares by code point (not locale-aware).
"""


def is_before(a: str, b: str) -> bool:
    return a < b


def sort_pair(a: str, b: str) -> tuple[str, str]:
    if a <= b:
        return (a, b)
    return (b, a)


def find_min_str(items: list[str]) -> str:
    if len(items) == 0:
        raise ValueError("empty list")
    result: str = items[0]
    for s in items:
        if s < result:
            result = s
    return result


def main() -> None:
    # Basic lexicographic ordering
    assert is_before("abc", "abd") == True   # differ at position 2
    assert is_before("abd", "abc") == False
    assert is_before("abc", "abc") == False  # equal, not less

    # Prefix ordering: shorter string is less if it's a prefix
    assert is_before("ab", "abc") == True
    assert is_before("abc", "ab") == False

    # Empty string is less than any non-empty string
    assert is_before("", "a") == True
    assert is_before("a", "") == False
    assert is_before("", "") == False

    # Case sensitivity: uppercase < lowercase in Unicode
    assert is_before("A", "a") == True   # ord('A')=65 < ord('a')=97
    assert is_before("Z", "a") == True   # ord('Z')=90 < ord('a')=97

    # Digit ordering
    assert is_before("1", "2") == True
    assert is_before("9", "10") == False  # "9" > "1" (first char comparison)

    # Sort pair
    p1: tuple[str, str] = sort_pair("banana", "apple")
    assert p1[0] == "apple"
    assert p1[1] == "banana"

    # Find minimum
    m: str = find_min_str(["cherry", "apple", "banana"])
    assert m == "apple"

    print(p1, m)


main()
