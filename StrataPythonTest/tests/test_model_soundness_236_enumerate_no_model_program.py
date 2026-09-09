# `enumerate()` has no model — manual index loop equivalent works if findings
# 156/203/169 are correct; desugar is mechanical
"""
`enumerate(iterable)` yields (index, element) pairs. It's not explicitly
IN or OUT of the subset, but `for i, x in enumerate(lst)` is a common
pattern that combines:
- range-based indexing (IN)
- element access (IN)
- tuple unpacking (may grow)

Without enumerate, the equivalent is:
    i = 0
    for x in lst:
        # use i and x
        i += 1

The model must handle this equivalent correctly. If enumerate IS
accepted, it needs a model that produces (int, element) pairs.

Uses ONLY confirmed-accepted constructs: for, list, int, while.
"""


def manual_enumerate(xs: list[str]) -> list[int]:
    """Manual equivalent of enumerate — always works."""
    indices: list[int] = []
    i: int = 0
    for x in xs:
        if x == "target":
            indices.append(i)
        i = i + 1
    return indices


def index_based_equivalent(xs: list[int]) -> int:
    """Index-based loop — equivalent to enumerate."""
    total: int = 0
    i: int = 0
    while i < len(xs):
        total = total + i * xs[i]  # weighted sum
        i = i + 1
    return total


def find_all_positions(xs: list[int], target: int) -> list[int]:
    """Find all indices where target appears."""
    positions: list[int] = []
    i: int = 0
    while i < len(xs):
        if xs[i] == target:
            positions.append(i)
        i = i + 1
    return positions


def indexed_transform(xs: list[int]) -> list[int]:
    """Transform elements using their index."""
    result: list[int] = []
    i: int = 0
    while i < len(xs):
        result.append(xs[i] + i)
        i = i + 1
    return result


def main() -> None:
    assert manual_enumerate(["a", "target", "b", "target"]) == [1, 3]
    assert index_based_equivalent([10, 20, 30]) == 0*10 + 1*20 + 2*30  # 80
    assert find_all_positions([1, 2, 3, 2, 1], 2) == [1, 3]
    assert indexed_transform([10, 20, 30]) == [10, 21, 32]

    print(manual_enumerate(["x", "target", "y"]),
          index_based_equivalent([10, 20, 30]),
          find_all_positions([5, 3, 5], 5))


main()
