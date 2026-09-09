# **PROMISE vs DELIVERY**: str.split() is IN but model returns Hole; subset's
# own example uses it — unverifiable
"""
SUBSET PROMISES str.split() IS IN — MODEL RETURNS HOLE

The subset document explicitly lists str.split() as IN and uses it
in the WORKED EXAMPLE (count_words). But finding 019 notes that
str.split() has no Laurel model — the result is unconstrained Hole.

This means: the subset's own example program CANNOT BE VERIFIED.
The verifier would say "cannot prove" for the count_words function
because split() returns Hole, and iterating over Hole is undefined.

This is a PROMISE vs DELIVERY gap: the subset says "we support this"
but the model doesn't implement it.
"""


def count_words(text: str) -> dict[str, int]:
    """FROM THE SUBSET DOCUMENT — the canonical example."""
    counts: dict[str, int] = {}
    for word in text.split():
        if word in counts:
            counts[word] = counts[word] + 1
        else:
            counts[word] = 1
    return counts


def first_word(text: str) -> str:
    """Extract first word — needs split() to return list[str]."""
    parts: list[str] = text.split()
    if len(parts) > 0:
        return parts[0]
    return ""


def word_count(text: str) -> int:
    """Count number of words — needs split() + len()."""
    return len(text.split())


def split_by_delimiter(text: str, delim: str) -> list[str]:
    """Split by specific delimiter."""
    return text.split(delim)


def main() -> None:
    # Test 1: count_words (the subset's own example)
    freq: dict[str, int] = count_words("hello world hello")
    assert freq["hello"] == 2
    assert freq["world"] == 1

    # Test 2: first word
    assert first_word("hello world") == "hello"
    assert first_word("") == ""

    # Test 3: word count
    assert word_count("a b c d") == 4
    assert word_count("") == 0

    # Test 4: split by delimiter
    parts: list[str] = split_by_delimiter("a,b,c", ",")
    assert parts == ["a", "b", "c"]

    print("all passed")


main()
