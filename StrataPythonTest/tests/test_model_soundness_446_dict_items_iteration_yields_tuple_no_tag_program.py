# `for k, v in d.items()` yields tuples — tuple has no `Any` tag; dict.items()
# iteration unrepresentable; desugar to `for k in d: v=d[k]`
"""
DICT.ITEMS() ITERATION YIELDS TUPLES — NO TUPLE TAG IN Any

The subset declares:
  - dict[str, int] is IN
  - dict.keys()/.values()/.items() iteration is IN (finding 188 confirms)
  - tuple[T1, T2, ...] is IN

But the Any datatype has NO from_tuple constructor:
  datatype Any { from_None, from_bool, from_int, from_float, from_str,
                 from_DictStrAny, from_ListAny, from_ClassInstance, 
                 from_Composite, exception }

When iterating `for k, v in d.items()`:
  CPython: each iteration yields a tuple (key, value)
  Model:   the iteration variable has type Any, but tuple has no tag
           → the yielded value is unrepresentable → Hole

This is distinct from finding 028 (tuple no representation) because
here the tuple is IMPLICITLY created by dict.items(), not by user code.
The user writes perfectly natural dict iteration code that the subset
explicitly allows, but the model cannot represent the intermediate value.

Even if we avoid tuple unpacking and use `for item in d.items()`:
  item has type tuple[str, int] — still no tag.
  item[0] and item[1] — subscript on unrepresentable value → Hole.
"""


def sum_values(d: dict[str, int]) -> int:
    """Sum all values by iterating .values() — this MIGHT work if
    values() returns a list-like iterable of ints."""
    total: int = 0
    for v in d.values():
        total = total + v
    return total


def collect_keys(d: dict[str, int]) -> list[str]:
    """Collect keys into a list — keys() returns str iterable."""
    result: list[str] = []
    for k in d.keys():
        result.append(k)
    return result


def sum_by_items(d: dict[str, int]) -> int:
    """Sum values using .items() iteration — requires tuple unpacking.
    
    CPython: for k, v in d.items() yields (str, int) tuples, unpacks them.
    Model: items() has no model; even if it did, tuple has no Any tag.
    """
    total: int = 0
    for k, v in d.items():
        total = total + v
    return total


def find_key_for_value(d: dict[str, int], target: int) -> str:
    """Find first key whose value matches target — requires items()."""
    for k, v in d.items():
        if v == target:
            return k
    return ""


def invert_dict(d: dict[str, int]) -> dict[int, str]:
    """Invert a dict — requires items() AND int-keyed dict (finding 029).
    Double unsoundness: items() yields unrepresentable tuples AND
    result dict has int keys with no DictIntAny."""
    result: dict[int, str] = {}
    for k, v in d.items():
        result[v] = k
    return result


def main() -> None:
    scores: dict[str, int] = {"alice": 95, "bob": 87, "carol": 92}

    # values() iteration — may work if model treats as list[int]
    assert sum_values(scores) == 274

    # keys() iteration — may work if model treats as list[str]
    keys: list[str] = collect_keys(scores)
    assert len(keys) == 3

    # items() iteration — REQUIRES tuple, which has no tag
    # CPython: works, total = 274
    # Model: items() returns Hole OR tuple has no tag → Hole
    assert sum_by_items(scores) == 274

    # items() with conditional — same issue
    assert find_key_for_value(scores, 87) == "bob"

    print(sum_values(scores), sum_by_items(scores),
          find_key_for_value(scores, 92))


main()
