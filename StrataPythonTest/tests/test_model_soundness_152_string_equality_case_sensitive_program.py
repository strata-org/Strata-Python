# String equality case-sensitive — must use SMT-LIB native `=` on String sort,
# not uninterpreted `str_eq`
"""
String equality (`==`) is case-sensitive: "Hello" != "hello". The model
must use exact string comparison (SMT-LIB `str.=` is case-sensitive).
If the model uses case-insensitive comparison or an uninterpreted
equality, it may report wrong results.
"""


def exact_match(a: str, b: str) -> bool:
    return a == b


def case_matters() -> bool:
    return "Hello" == "hello"  # False! Case-sensitive


def find_exact(lst: list[str], target: str) -> int:
    i: int = 0
    for s in lst:
        if s == target:
            return i
        i = i + 1
    return -1


def count_matches(lst: list[str], target: str) -> int:
    count: int = 0
    for s in lst:
        if s == target:
            count = count + 1
    return count


def main() -> None:
    # Case-sensitive equality
    assert exact_match("hello", "hello") == True
    assert exact_match("Hello", "hello") == False
    assert exact_match("", "") == True
    assert exact_match("a", "A") == False

    # Case matters
    assert case_matters() == False

    # Find exact (case-sensitive)
    words: list[str] = ["Hello", "world", "hello", "World"]
    assert find_exact(words, "hello") == 2  # not 0 ("Hello" != "hello")
    assert find_exact(words, "Hello") == 0

    # Count (case-sensitive)
    assert count_matches(["a", "A", "a", "A", "a"], "a") == 3

    print(exact_match("Hi", "hi"), case_matters(), find_exact(words, "hello"))


main()
