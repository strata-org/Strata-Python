# LIST NEGATIVE INDEX WRITE — NO INDEX WRAPPING IN List_set
"""
LIST NEGATIVE INDEX WRITE — NO INDEX WRAPPING IN List_set

The subset allows:
  - List element assignment lst[i] = v (IN — finding 078)
  - Negative indexing lst[-1] (IN — finding 020/431 cover reads)
  - Arithmetic on indices (IN)

The NOVEL gap: `lst[-1] = 99` writes to the LAST element in CPython
(index wrapping: -1 → len(lst)-1). But `List_set(lst, -1, v)` in the
model has no index-wrapping logic — it either:
  (a) Writes to a non-existent position (index -1 doesn't exist in cons-list)
  (b) Returns Hole or unchanged list
  (c) Raises an error (wrong — CPython succeeds)

Findings 020 and 431 cover negative index READS (List_get). Finding 078
covers element WRITES with positive indices. But the COMBINATION —
negative index in a WRITE — is not covered. The wrapping logic must be
applied to BOTH reads and writes.

CPython: lst = [10, 20, 30]; lst[-1] = 99 → [10, 20, 99]
Model:   List_set(lst, -1, 99) → unchanged list or Hole (no wrapping)

DISTINCT FROM:
  - Finding 020 (negative index read) — covers List_get, not List_set
  - Finding 078 (element assignment) — covers positive indices only
  - Finding 431 (negative index wraps) — covers reads, not writes
  - Finding 341 (list subscript augmented assign) — covers +=, not plain =
"""


def set_last_element(lst: list[int], value: int) -> list[int]:
    """lst[-1] = value sets the last element."""
    lst[-1] = value
    return lst
    # CPython: [1,2,3] with value=99 → [1, 2, 99]
    # Model: List_set(lst, -1, 99) → no wrapping → unchanged or Hole


def set_second_to_last(lst: list[int], value: int) -> list[int]:
    """lst[-2] = value sets the second-to-last element."""
    lst[-2] = value
    return lst
    # CPython: [1,2,3] with value=99 → [1, 99, 3]
    # Model: List_set(lst, -2, 99) → no wrapping → wrong position


def swap_first_last(lst: list[int]) -> list[int]:
    """Swap first and last elements using negative indexing."""
    temp: int = lst[0]
    lst[0] = lst[-1]
    lst[-1] = temp
    return lst
    # CPython: [1,2,3] → [3, 2, 1]
    # Model: lst[-1] = temp fails (no wrapping on write)
    #         result: [3, 2, 3] or Hole


def reverse_in_place(lst: list[int]) -> list[int]:
    """Reverse using negative index writes."""
    n: int = len(lst)
    i: int = 0
    while i < n // 2:
        temp: int = lst[i]
        lst[i] = lst[-(i + 1)]    # negative index READ
        lst[-(i + 1)] = temp       # negative index WRITE — the gap!
        i = i + 1
    return lst
    # CPython: [1,2,3,4] → [4,3,2,1]
    # Model: negative index writes fail → partial or no reversal


def set_from_end(lst: list[int], offset: int, value: int) -> list[int]:
    """Set element at offset from end: lst[-offset] = value."""
    lst[-offset] = value
    return lst
    # CPython: [10,20,30,40,50] with offset=3, value=99 → [10,20,99,40,50]
    # Model: List_set(lst, -3, 99) → no wrapping → wrong


def main() -> None:
    assert set_last_element([1, 2, 3], 99) == [1, 2, 99]
    assert set_second_to_last([1, 2, 3], 99) == [1, 99, 3]
    assert swap_first_last([1, 2, 3]) == [3, 2, 1]
    assert reverse_in_place([1, 2, 3, 4]) == [4, 3, 2, 1]
    assert set_from_end([10, 20, 30, 40, 50], 3, 99) == [10, 20, 99, 40, 50]
    print("All passed")


main()
