# `List_get(List_set(xs, i, v), j) == List_get(xs, j)` frame axiom missing —
# writing at i destroys knowledge of all other indices
"""
CONS-LIST SET THEN GET AT DIFFERENT INDEX — PRESERVATION AXIOM MISSING

CPython: xs = [10, 20, 30]; xs[1] = 99; xs[0] == 10 (unchanged!)
         Writing at index 1 does NOT affect index 0.

Model:   xs' = List_set(xs, 1, 99)
         List_get(xs', 0) == ???

         Finding 253 covers: List_get(List_set(xs, i, v), i) == v
         (read-back at SAME index — the "read-over-write" axiom)

         This finding covers: List_get(List_set(xs, i, v), j) == List_get(xs, j)
         for j ≠ i (read at DIFFERENT index — the "frame" axiom)

         Without the frame axiom, writing at index 1 could DESTROY
         the value at index 0 from the solver's perspective.
         The solver treats List_get(xs', 0) as unconstrained.

These are the TWO McCarthy axioms for arrays:
  get(set(a, i, v), i) == v           (finding 253)
  get(set(a, i, v), j) == get(a, j)   when i ≠ j (THIS finding)
Both are needed for correct list reasoning.
"""


def write_preserves_other(xs: list[int], write_idx: int, read_idx: int, val: int) -> int:
    """Writing at one index preserves value at another."""
    xs[write_idx] = val
    return xs[read_idx]


def swap_elements(xs: list[int], i: int, j: int) -> list[int]:
    """Swap requires both axioms: read-back AND preservation."""
    temp: int = xs[i]
    xs[i] = xs[j]    # write at i; must preserve j
    xs[j] = temp     # write at j; must preserve i (which now has old xs[j])
    return xs


def modify_one_preserve_rest() -> list[int]:
    """Modify middle element, verify endpoints unchanged."""
    xs: list[int] = [1, 2, 3, 4, 5]
    xs[2] = 99
    # xs[0] must still be 1, xs[4] must still be 5
    return xs


def main() -> None:
    # Test 1: write at index 1, read at index 0
    data: list[int] = [10, 20, 30]
    result: int = write_preserves_other(data, 1, 0, 99)
    # CPython: 10 (index 0 unchanged)
    # Model without frame axiom: unconstrained (could be anything)
    assert result == 10

    # Test 2: write at index 0, read at index 2
    data2: list[int] = [10, 20, 30]
    result2: int = write_preserves_other(data2, 0, 2, 99)
    assert result2 == 30

    # Test 3: swap
    data3: list[int] = [1, 2, 3]
    swapped: list[int] = swap_elements(data3, 0, 2)
    assert swapped == [3, 2, 1]

    # Test 4: modify middle, check endpoints
    modified: list[int] = modify_one_preserve_rest()
    assert modified[0] == 1
    assert modified[2] == 99
    assert modified[4] == 5

    print("all passed")


main()
