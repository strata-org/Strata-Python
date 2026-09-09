# **INTEGRATION TEST**: subset's `count_words` example uses 5 features with
# model gaps; serves as milestone — when it verifies, core model works
"""
SUBSET EXAMPLE count_words USES SPLIT — ENTIRE FUNCTION UNVERIFIABLE

The subset document's WORKED EXAMPLE is:

    def count_words(text: str) -> dict[str, int]:
        counts: dict[str, int] = {}
        for word in text.split():
            if word in counts:
                counts[word] = counts[word] + 1
            else:
                counts[word] = 1
        return counts

This function uses FIVE features that have model gaps:
1. str.split() → Hole (finding 019/396)
2. for word in <Hole> → undefined iteration (finding 363)
3. word in counts → DictStrAny_contains (finding 367 — no axiom after set)
4. counts[word] + 1 → dict value type lost (finding 352)
5. counts[word] = ... → dict rebinding in loop (finding 146/370)

The subset's OWN EXAMPLE cannot be verified by the current model.
This is the ultimate integration test for the encoding.
"""


def count_words(text: str) -> dict[str, int]:
    """The subset's canonical example — verbatim."""
    counts: dict[str, int] = {}
    for word in text.split():
        if word in counts:
            counts[word] = counts[word] + 1
        else:
            counts[word] = 1
    return counts


def most_common_word(text: str) -> str:
    """Extension: find the most frequent word."""
    counts: dict[str, int] = count_words(text)
    best: str = ""
    best_count: int = 0
    for word in text.split():
        if word in counts:
            if counts[word] > best_count:
                best = word
                best_count = counts[word]
    return best


def unique_word_count(text: str) -> int:
    """Count unique words."""
    return len(count_words(text))


def main() -> None:
    # Test 1: basic word counting
    freq: dict[str, int] = count_words("the cat sat on the mat")
    assert freq["the"] == 2
    assert freq["cat"] == 1
    assert freq["sat"] == 1
    assert freq["on"] == 1
    assert freq["mat"] == 1

    # Test 2: single word
    freq2: dict[str, int] = count_words("hello")
    assert freq2["hello"] == 1

    # Test 3: repeated word
    freq3: dict[str, int] = count_words("go go go")
    assert freq3["go"] == 3

    # Test 4: unique count
    assert unique_word_count("a b c a b") == 3

    # Test 5: most common
    assert most_common_word("a b a c a") == "a"

    print("all passed")


main()
