# `in` operator right-operand tag dispatch — str-in-str (substring), str-in-
# list (element), str-in-dict (key); three algorithms, one operator
"""
`in` OPERATOR TYPE DISPATCH — str-in-str vs str-in-list vs str-in-dict

CPython: "ab" in "abc"     → True (SUBSTRING check)
         "ab" in ["ab","c"] → True (ELEMENT equality check)
         "ab" in {"ab": 1}  → True (KEY membership check)

         Three completely different algorithms based on the RIGHT operand's type.

Model:   The `in` operator must dispatch on the TAG of the right operand:
         - from_str: substring containment (SMT-LIB str.contains)
         - from_ListAny: element equality scan (List_contains)
         - from_DictStrAny: key membership (DictStrAny_contains)

         If the translator uses a single `PIn` function that doesn't
         dispatch on the right operand's tag, it will use the wrong
         algorithm. E.g., using List_contains on a string, or
         substring search on a list.

Finding 095 notes dict `in` checks keys not values.
Finding 046 notes string `in` is substring.
Finding 304 catalogs the dispatch.
This finding provides the CONCRETE program showing all three in one
function, demonstrating the tag-dispatch requirement.
"""


def substring_check(needle: str, haystack: str) -> bool:
    """str in str → substring containment."""
    return needle in haystack


def element_check(item: str, items: list[str]) -> bool:
    """str in list → element equality."""
    return item in items


def key_check(key: str, mapping: dict[str, int]) -> bool:
    """str in dict → key membership."""
    return key in mapping


def combined_search(query: str, text: str, tags: list[str], meta: dict[str, int]) -> str:
    """All three `in` variants in one function — dispatch must be correct."""
    if query in text:
        return "found in text"
    elif query in tags:
        return "found in tags"
    elif query in meta:
        return "found in meta"
    else:
        return "not found"


def main() -> None:
    # Test 1: substring (str in str)
    assert substring_check("bc", "abcd")
    assert not substring_check("xy", "abcd")
    # "b" in "abc" → True (single char is substring)
    assert substring_check("b", "abc")

    # Test 2: element (str in list)
    fruits: list[str] = ["apple", "banana", "cherry"]
    assert element_check("banana", fruits)
    assert not element_check("grape", fruits)
    # CRITICAL: "an" in ["banana"] → False (element equality, not substring!)
    assert not element_check("an", fruits)

    # Test 3: key (str in dict)
    scores: dict[str, int] = {"alice": 95, "bob": 87}
    assert key_check("alice", scores)
    assert not key_check("carol", scores)

    # Test 4: combined — same query, different containers
    assert combined_search("hello", "say hello world", ["hi", "hey"], {"greet": 1}) == "found in text"
    assert combined_search("hi", "say hello world", ["hi", "hey"], {"greet": 1}) == "found in tags"
    assert combined_search("greet", "say hello world", ["hi", "hey"], {"greet": 1}) == "found in meta"
    assert combined_search("xyz", "say hello world", ["hi", "hey"], {"greet": 1}) == "not found"

    print("all passed")


main()
