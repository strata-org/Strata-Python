# `list.extend()` / loop-append pattern — no length axioms; `len(result) ==
# len(a) + len(b)` unprovable; blocks ALL list-building verification
"""
LIST.EXTEND() — NO MODEL, LENGTH RELATIONSHIP UNPROVABLE

The subset allows list.append() (finding 009 covers its model gap).
list.extend() is also a common list method that adds ALL elements
from another iterable.

CPython:
  a = [1, 2]
  a.extend([3, 4, 5])
  # a is now [1, 2, 3, 4, 5]
  # len(a) == 5 == 2 + 3

Model:
  Under value semantics with rebinding:
    a = List_extend(a, [3, 4, 5])
  
  But List_extend is uninterpreted (no axioms), so:
  - len(a) after extend is unconstrained (Hole)
  - a[0] after extend is unconstrained (Hole)
  - The relationship len(result) == len(original) + len(extension) is unprovable

This is distinct from:
  - Finding 004 (extend mutates in place) — that's about aliasing
  - Finding 074 (list + list no model) — that's about the + operator
  - Finding 417 (concat length) — that's about + operator length

list.extend() is the METHOD form of concatenation. Under value semantics
with rebinding (a = a.extend(other)), the model needs axioms for:
  1. len(extend(a, b)) == len(a) + len(b)
  2. extend(a, b)[i] == a[i] for i < len(a)
  3. extend(a, b)[i] == b[i - len(a)] for len(a) <= i < len(a)+len(b)

Without these, any code that builds a list via extend and then checks
bounds or accesses elements produces Hole.

ADDITIONAL ISSUE: list.extend() returns None in CPython (mutates in place).
Under value semantics, it must return the new list. The translator must
handle this return-value mismatch (same issue as append, finding 009).
"""


def merge_sorted_halves(left: list[int], right: list[int]) -> list[int]:
    """Merge two lists by extending — common pattern."""
    result: list[int] = []
    for x in left:
        result.append(x)
    for x in right:
        result.append(x)
    return result


def build_with_extend(parts: list[list[int]]) -> list[int]:
    """Build a flat list from list of lists.
    
    Note: list[list[int]] is a list whose elements are lists.
    Under the model, elements are from_ListAny — valid tag.
    """
    result: list[int] = []
    for part in parts:
        # In CPython: result.extend(part) mutates result
        # Under value semantics: result = extend(result, part)
        for x in part:
            result.append(x)
    return result


def extend_then_check_length(base: list[int], extra: list[int]) -> bool:
    """Extend a list then verify length relationship.
    
    CPython: len(result) == len(base) + len(extra) — always true
    Model: len(result) is unconstrained — cannot prove this
    """
    result: list[int] = []
    for x in base:
        result.append(x)
    for x in extra:
        result.append(x)
    # The critical assertion: length is sum of parts
    return len(result) == len(base) + len(extra)


def extend_preserves_prefix(original: list[int], suffix: list[int]) -> bool:
    """After extending, original elements are still accessible.
    
    CPython: result[0] == original[0] — always true (if original non-empty)
    Model: result[0] is unconstrained after extend — cannot prove
    """
    result: list[int] = [original[0]]
    for x in suffix:
        result.append(x)
    # First element should still be original[0]
    return result[0] == original[0]


def flatten_and_sum(nested: list[list[int]]) -> int:
    """Flatten nested list and sum — requires extend semantics for bounds."""
    flat: list[int] = []
    for sublist in nested:
        for x in sublist:
            flat.append(x)
    total: int = 0
    for x in flat:
        total = total + x
    return total


def main() -> None:
    # Basic merge
    merged: list[int] = merge_sorted_halves([1, 2, 3], [4, 5, 6])
    assert merged == [1, 2, 3, 4, 5, 6]
    assert len(merged) == 6

    # Length relationship
    assert extend_then_check_length([1, 2], [3, 4, 5]) == True
    assert extend_then_check_length([], [1, 2, 3]) == True
    assert extend_then_check_length([1, 2, 3], []) == True

    # Prefix preservation
    assert extend_preserves_prefix([10, 20], [30, 40]) == True

    # Flatten and sum
    assert flatten_and_sum([[1, 2], [3, 4], [5]]) == 15
    assert flatten_and_sum([[], [1], []]) == 1

    print(len(merged), extend_then_check_length([1], [2, 3]),
          flatten_and_sum([[1, 2], [3]]))


main()
