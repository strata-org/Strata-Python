# Bounds check pattern — `if 0 <= i and i < len(lst): lst[i]` — guard must
# discharge index precondition
"""
The bounds-check pattern `if 0 <= i and i < len(lst): lst[i]` is the
standard way to safely access list elements. The model must:
1. Evaluate `0 <= i` → from_bool
2. Short-circuit `and` (finding 044)
3. Evaluate `i < len(lst)` → from_bool
4. Use both facts to prove `lst[i]` is safe (index in bounds)

If the verifier can't connect the guard to the subsequent access,
it reports a false positive "possible IndexError."
"""


def safe_get(lst: list[int], i: int) -> int:
    if 0 <= i and i < len(lst):
        return lst[i]  # safe: bounds proven by guard
    return -1


def safe_set(lst: list[int], i: int, val: int) -> list[int]:
    if 0 <= i and i < len(lst):
        lst[i] = val  # safe: bounds proven
    return lst


def sum_range(lst: list[int], start: int, end: int) -> int:
    total: int = 0
    i: int = start
    while i < end and i < len(lst):
        if i >= 0:
            total = total + lst[i]
        i = i + 1
    return total


def main() -> None:
    data: list[int] = [10, 20, 30, 40, 50]

    # Safe get: in bounds
    assert safe_get(data, 0) == 10
    assert safe_get(data, 4) == 50

    # Safe get: out of bounds
    assert safe_get(data, -1) == -1
    assert safe_get(data, 5) == -1

    # Safe set
    result: list[int] = safe_set([1, 2, 3], 1, 99)
    assert result[1] == 99

    # Sum range
    assert sum_range(data, 1, 4) == 90  # 20+30+40

    print(safe_get(data, 2), safe_get(data, 10), sum_range(data, 0, 3))


main()
