# `len(dict)` after key overwrite — association list keeps shadowed
# duplicates, `DictStrAny_len` counts all entries not unique keys
"""
DictStrAny is an association list using cons. When a key is overwritten
(d[k] = new_val), the new entry is prepended but the OLD entry remains.
DictStrAny_get finds the first match (correct), but DictStrAny_len counts
ALL entries including shadowed duplicates (wrong).
Python's len(d) returns the number of UNIQUE keys.
"""


def build_and_count(keys: list[str]) -> int:
    d: dict[str, int] = {}
    for k in keys:
        d[k] = 1  # may overwrite existing key
    return len(d)


def overwrite_test() -> int:
    d: dict[str, int] = {}
    d["x"] = 1
    d["y"] = 2
    d["x"] = 3  # overwrite "x"
    # Python: len(d) == 2 (keys are "x" and "y")
    # Model: DictStrAny has 3 cons cells (x=3, y=2, x=1)
    #         DictStrAny_len counts 3
    return len(d)


def main() -> None:
    # Repeated keys: only unique keys count
    n: int = build_and_count(["a", "b", "a", "c", "b"])
    # Python: {"a": 1, "b": 1, "c": 1} → len == 3
    assert n == 3

    # Overwrite: len doesn't increase
    m: int = overwrite_test()
    assert m == 2

    print(n, m)


main()
