# Dict iteration order — assoc-list prepend yields reverse insertion order;
# CPython guarantees insertion order since 3.7
"""
Python 3.7+ guarantees dict iteration order matches insertion order.
`for k in d` yields keys in the order they were first inserted.
The association list model (prepend on set) naturally yields keys in
REVERSE insertion order (most recent first). This diverges from CPython.
"""


def get_keys_in_order(d: dict[str, int]) -> list[str]:
    result: list[str] = []
    for k in d:
        result = result + [k]
    return result


def first_key(d: dict[str, int]) -> str:
    for k in d:
        return k
    return ""


def build_ordered() -> dict[str, int]:
    d: dict[str, int] = {}
    d["first"] = 1
    d["second"] = 2
    d["third"] = 3
    return d


def main() -> None:
    # Literal order preserved
    d1: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    keys1: list[str] = get_keys_in_order(d1)
    assert keys1 == ["a", "b", "c"]  # insertion order

    # Built incrementally: insertion order preserved
    d2: dict[str, int] = build_ordered()
    keys2: list[str] = get_keys_in_order(d2)
    assert keys2 == ["first", "second", "third"]

    # First key is the first inserted
    assert first_key(d2) == "first"

    # Overwrite doesn't change order (key stays in original position)
    d3: dict[str, int] = {"x": 1, "y": 2, "z": 3}
    d3["y"] = 99  # overwrite doesn't move "y"
    keys3: list[str] = get_keys_in_order(d3)
    assert keys3 == ["x", "y", "z"]  # order unchanged

    print(keys1, keys2, first_key(d2))


main()
