# Dict construction in loop — `d[k] = v` must rebind `d` each iteration;
# without rebinding, dict never grows
"""
Building a dict in a loop (`for item in lst: d[key] = value`) is the
standard pattern for constructing dicts from data. Under pure-function
value semantics, each `d[key] = value` creates a NEW DictStrAny. The
variable `d` must be rebound after each assignment.

If the translator doesn't rebind `d` after `d[key] = value`, the dict
never grows — each assignment operates on the original empty dict.
"""


def build_index(names: list[str]) -> dict[str, int]:
    d: dict[str, int] = {}
    i: int = 0
    for name in names:
        d[name] = i
        i = i + 1
    return d


def count_chars(s: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    i: int = 0
    while i < len(s):
        c: str = s[i]
        if c in counts:
            counts[c] = counts[c] + 1
        else:
            counts[c] = 1
        i = i + 1
    return counts


def invert_dict(d: dict[str, int]) -> dict[str, str]:
    """Swap keys and values (values become string keys)."""
    result: dict[str, str] = {}
    for k in d:
        result[str(d[k])] = k
    return result


def main() -> None:
    # Build index
    idx: dict[str, int] = build_index(["a", "b", "c"])
    assert idx["a"] == 0
    assert idx["b"] == 1
    assert idx["c"] == 2
    assert len(idx) == 3

    # Count characters
    counts: dict[str, int] = count_chars("hello")
    assert counts["h"] == 1
    assert counts["l"] == 2
    assert counts["o"] == 1

    # Invert
    original: dict[str, int] = {"x": 1, "y": 2}
    inverted: dict[str, str] = invert_dict(original)
    assert inverted["1"] == "x"
    assert inverted["2"] == "y"

    print(idx["a"], counts["l"], len(idx))


main()
