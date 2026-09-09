# For-loop element mutation invisible — `for x in lst: x.field = v` modifies
# copy not list element; AST must reject mutable loop-var mutation
"""
In `for x in lst`, the loop variable `x` is a COPY of each element
(under value semantics). Modifying `x` inside the loop body does NOT
modify the list element.

    for x in items:
        x.value = 99  # modifies the COPY, not items[i]!

In CPython, `x` IS items[i] (same reference). Modification is visible.
Under value semantics, `x` is a copy. Modification is lost.

This is a specific instance of "no aliasing" applied to for-loop
iteration variables. The AST checker must reject this pattern.

Uses ONLY confirmed-accepted constructs: @dataclass, for, list, int.
"""
from dataclasses import dataclass


@dataclass
class Item:
    name: str
    count: int


def modify_loop_var_lost() -> list[Item]:
    """Modifying loop variable doesn't affect list (value semantics).
    In CPython: DOES affect list (reference semantics).
    THIS PATTERN DIVERGES."""
    items: list[Item] = [
        Item(name="a", count=1),
        Item(name="b", count=2),
        Item(name="c", count=3),
    ]
    for item in items:
        item.count = 0  # CPython: modifies list element
                        # Model: modifies copy, list unchanged
    return items


def correct_pattern_index_based() -> list[Item]:
    """Correct: use index-based modification with write-back."""
    items: list[Item] = [
        Item(name="a", count=1),
        Item(name="b", count=2),
        Item(name="c", count=3),
    ]
    i: int = 0
    while i < len(items):
        items[i] = Item(name=items[i].name, count=0)
        i = i + 1
    return items


def correct_pattern_build_new() -> list[Item]:
    """Correct: build a new list with modified elements."""
    items: list[Item] = [
        Item(name="a", count=1),
        Item(name="b", count=2),
    ]
    result: list[Item] = []
    for item in items:
        result.append(Item(name=item.name, count=item.count * 2))
    return result


def read_only_loop_safe() -> int:
    """Reading loop variable is always safe (no mutation)."""
    items: list[Item] = [Item(name="x", count=5), Item(name="y", count=3)]
    total: int = 0
    for item in items:
        total = total + item.count  # read-only: safe
    return total


def main() -> None:
    # Diverging pattern (CPython modifies, model doesn't)
    diverging: list[Item] = modify_loop_var_lost()
    # CPython: all counts are 0
    assert diverging[0].count == 0  # True in CPython
    # Model would say: diverging[0].count == 1 (unchanged)

    # Correct patterns
    correct1: list[Item] = correct_pattern_index_based()
    assert correct1[0].count == 0
    assert correct1[1].count == 0
    assert correct1[2].count == 0

    correct2: list[Item] = correct_pattern_build_new()
    assert correct2[0].count == 2
    assert correct2[1].count == 4

    # Read-only is safe
    assert read_only_loop_safe() == 8

    print(correct1[0].count, correct2[0].count, read_only_loop_safe())


main()
