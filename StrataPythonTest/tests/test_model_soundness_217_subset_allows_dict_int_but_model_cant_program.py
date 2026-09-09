# Subset allows `dict[int, V]` but model only has DictStrAny — promise vs
# delivery; frequency counters unrepresentable
"""
The subset explicitly says:
  "dict[K, V] for K ∈ {str, int}"

But the model only has `from_DictStrAny` — string keys only.
This is a PROMISE vs DELIVERY mismatch: the subset promises int keys
but the encoding can't represent them.

Finding 175 identified the representation gap. This finding focuses on
the SUBSET DEFINITION aspect: either the subset must narrow (move
dict[int, V] to OUT) or the model must extend (add DictIntAny).

Uses ONLY confirmed-accepted constructs: dict[int, str], int.
"""


def frequency_counter(xs: list[int]) -> dict[int, int]:
    """The most common use of dict[int, V]: counting occurrences."""
    counts: dict[int, int] = {}
    for x in xs:
        if x in counts:
            counts[x] = counts[x] + 1
        else:
            counts[x] = 1
    return counts


def index_to_value(xs: list[str]) -> dict[int, str]:
    """Map index → value. Common pattern."""
    result: dict[int, str] = {}
    i: int = 0
    for x in xs:
        result[i] = x
        i = i + 1
    return result


def enum_like_mapping() -> dict[int, str]:
    """Status codes → descriptions."""
    d: dict[int, str] = {}
    d[200] = "OK"
    d[404] = "Not Found"
    d[500] = "Server Error"
    return d


def main() -> None:
    counts: dict[int, int] = frequency_counter([1, 2, 1, 3, 2, 1])
    assert counts[1] == 3
    assert counts[2] == 2
    assert counts[3] == 1

    idx: dict[int, str] = index_to_value(["a", "b", "c"])
    assert idx[0] == "a"
    assert idx[2] == "c"

    codes: dict[int, str] = enum_like_mapping()
    assert codes[200] == "OK"
    assert codes[404] == "Not Found"

    print(counts[1], idx[0], codes[404])


main()
