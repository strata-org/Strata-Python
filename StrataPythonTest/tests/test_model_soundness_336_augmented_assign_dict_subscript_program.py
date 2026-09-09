# `d[k] += 1` augmented assign on dict subscript — requires 4-step read-
# modify-write-rebind; translator likely treats as no-op on dict
"""
AUGMENTED ASSIGNMENT ON DICT SUBSCRIPT: d[k] += 1

CPython: d["x"] += 1 desugars to d["x"] = d["x"] + 1 (in-place on dict)
         After: d["x"] == 2

Model:   d[k] += v requires:
         1. DictStrAny_get(d, k) → old_val
         2. PAdd(old_val, v) → new_val
         3. DictStrAny_set(d, k, new_val) → d'
         4. Rebind d to d'

         But the translator likely desugars AugAssign with Subscript target
         as a simple PAdd without the get/set/rebind chain. The dict is
         never updated — d["x"] remains 1.

Root cause: AugAssign translation handles Name targets (x += 1 → x = x + 1)
but Subscript targets (d[k] += 1) require a 4-step read-modify-write-rebind
that the translator doesn't implement.
"""


def count_chars(s: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for ch in s:
        if ch in counts:
            counts[ch] += 1  # THIS IS THE BUG: augmented assign on subscript
        else:
            counts[ch] = 1
    return counts


def accumulate(values: list[int]) -> dict[str, int]:
    result: dict[str, int] = {"total": 0, "count": 0}
    for v in values:
        result["total"] += v   # compound subscript augmented assign
        result["count"] += 1
    return result


def main() -> None:
    # Test 1: character counting
    freq: dict[str, int] = count_chars("aab")
    # CPython: {"a": 2, "b": 1}
    # Model:   {"a": 1, "b": 1} (the += never updates the dict)
    assert freq["a"] == 2
    assert freq["b"] == 1

    # Test 2: accumulation
    acc: dict[str, int] = accumulate([10, 20, 30])
    # CPython: {"total": 60, "count": 3}
    # Model:   {"total": 0, "count": 0} (augmented assigns are no-ops)
    assert acc["total"] == 60
    assert acc["count"] == 3

    print(freq)
    print(acc)


main()
