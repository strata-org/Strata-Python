# Augmented assignment target (`a[f()] += x`) evaluated once in CPython —
# naive desugar evaluates `f()` twice
"""
In `a[i] += x`, CPython evaluates `a` and `i` exactly ONCE, then
performs: tmp = a[i]; tmp2 = tmp + x; a[i] = tmp2. A naive desugaring
to `a[i] = a[i] + x` evaluates `a` and `i` TWICE. If either has side
effects (e.g., `i` is a function call), the double evaluation diverges.

This also applies to `obj.field += x` where `obj` is a complex expression.
"""
from dataclasses import dataclass


@dataclass
class IndexTracker:
    calls: int

    def next_index(self: "IndexTracker") -> int:
        idx: int = self.calls
        self.calls = self.calls + 1
        return idx


def increment_at(lst: list[int], tracker: IndexTracker) -> None:
    # tracker.next_index() should be called ONCE
    # CPython: evaluates next_index() once, uses result for both get and set
    lst[tracker.next_index()] += 10


def double_increment(lst: list[int], i: int) -> None:
    # Simple case: i is pure, no issue with double eval
    lst[i] += 1


def dict_augmented(d: dict[str, int], key: str) -> None:
    # d[key] += 1: key evaluated once
    d[key] += 1


def main() -> None:
    # Simple augmented assignment on list (no side effects in index)
    data: list[int] = [10, 20, 30, 40]
    double_increment(data, 1)
    assert data[1] == 21

    # Side-effecting index: next_index() called exactly once
    tracker: IndexTracker = IndexTracker(calls=0)
    values: list[int] = [100, 200, 300]

    increment_at(values, tracker)
    # CPython: next_index() returns 0 (calls becomes 1)
    #          values[0] = values[0] + 10 = 110
    assert values == [110, 200, 300]
    assert tracker.calls == 1  # Model (double eval): calls == 2

    increment_at(values, tracker)
    # CPython: next_index() returns 1 (calls becomes 2)
    #          values[1] = values[1] + 10 = 210
    assert values == [110, 210, 300]
    assert tracker.calls == 2  # Model (double eval): calls == 4

    # Dict augmented assignment
    counts: dict[str, int] = {"a": 5, "b": 10}
    dict_augmented(counts, "a")
    assert counts["a"] == 6

    print(values, tracker.calls)


main()
