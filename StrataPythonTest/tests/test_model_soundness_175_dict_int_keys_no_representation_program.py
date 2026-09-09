# `from_DictStrAny` only supports string keys — `dict[int, V]` is IN subset
# but has no representation; needs `DictIntAny`
"""
The `Any` datatype has `from_DictStrAny(as_Dict: DictStrAny)` — the dict
representation uses STRING keys only. But the Frontend subset says:

    dict[K, V] for K ∈ {str, int}

So `dict[int, str]` is IN the subset but has NO representation in the
model. `DictStrAny` cannot store integer keys.

This means:
- `{1: "one", 2: "two"}` cannot be constructed
- `d[42]` where d is dict[int, str] cannot be modeled
- `42 in d` cannot be checked
- Frequency counters (`counts[n] = counts.get(n, 0) + 1`) fail

Uses ONLY confirmed-accepted constructs: dict[int, str], int, function def.
"""


def int_key_lookup(d: dict[int, str], key: int) -> str:
    return d[key]


def int_key_membership(d: dict[int, str], key: int) -> bool:
    return key in d


def build_int_dict() -> dict[int, str]:
    d: dict[int, str] = {}
    d[1] = "one"
    d[2] = "two"
    d[3] = "three"
    return d


def count_occurrences(xs: list[int]) -> dict[int, int]:
    """Classic frequency counter — requires int keys."""
    counts: dict[int, int] = {}
    for x in xs:
        if x in counts:
            counts[x] = counts[x] + 1
        else:
            counts[x] = 1
    return counts


def index_mapping(xs: list[str]) -> dict[int, str]:
    """Map index → element."""
    result: dict[int, str] = {}
    i: int = 0
    for x in xs:
        result[i] = x
        i = i + 1
    return result


def main() -> None:
    # Build and lookup
    d: dict[int, str] = build_int_dict()
    assert int_key_lookup(d, 1) == "one"
    assert int_key_lookup(d, 3) == "three"

    # Membership
    assert int_key_membership(d, 2) == True
    assert int_key_membership(d, 99) == False

    # Frequency counter
    counts: dict[int, int] = count_occurrences([1, 2, 1, 3, 2, 1])
    assert counts[1] == 3
    assert counts[2] == 2
    assert counts[3] == 1

    # Index mapping
    idx_map: dict[int, str] = index_mapping(["a", "b", "c"])
    assert idx_map[0] == "a"
    assert idx_map[2] == "c"

    print(int_key_lookup(d, 1), len(d), counts[1])


main()
