# Dict value access type lost — `d[k]` from `dict[str, int]` returns untyped
# Any; no `isfrom_int` assertion; all value operations → Hole
"""
DICT VALUE ACCESS TYPE LOST — d[k] FROM dict[str, int] HAS NO TAG ASSERTION

CPython: d: dict[str, int] = {"x": 1}
         d["x"] → 1 (int, guaranteed by type annotation)

Model:   d is from_DictStrAny(assoc_list)
         d["x"] → DictStrAny_get(assoc_list, "x") → returns Any
         NO assertion that result is from_int
         Subsequent d["x"] + 1 → PAdd(unknown_tag, from_int(1)) → Hole

This is the DICT parallel of finding 350 (list element type lost).
The generic value type in dict[str, V] is lost at the access boundary.
"""


def get_port(config: dict[str, int]) -> int:
    """Dict value access needs tag assertion."""
    return config["port"]


def sum_values(d: dict[str, int]) -> int:
    """Iterate dict values — each needs tag assertion."""
    total: int = 0
    for k in d:
        total += d[k]  # d[k] returns Any; needs isfrom_int
    return total


def increment_all(d: dict[str, int], amount: int) -> dict[str, int]:
    """Read value, do arithmetic, write back."""
    result: dict[str, int] = {}
    for k in d:
        val: int = d[k]  # val: int annotation, but model has no tag assert
        result[k] = val + amount  # PAdd(unknown, from_int) → Hole
    return result


def max_value(d: dict[str, int]) -> int:
    """Comparison on dict values."""
    best: int = 0
    first: bool = True
    for k in d:
        v: int = d[k]
        if first:
            best = v
            first = False
        elif v > best:  # PLt(unknown, unknown) → Hole
            best = v
    return best


def main() -> None:
    config: dict[str, int] = {"port": 8080, "timeout": 30}

    # Test 1: simple access
    assert get_port(config) == 8080

    # Test 2: sum values
    assert sum_values(config) == 8110

    # Test 3: increment all
    inc: dict[str, int] = increment_all(config, 1)
    assert inc["port"] == 8081
    assert inc["timeout"] == 31

    # Test 4: max value
    scores: dict[str, int] = {"alice": 95, "bob": 87, "carol": 92}
    assert max_value(scores) == 95

    print("all passed")


main()
