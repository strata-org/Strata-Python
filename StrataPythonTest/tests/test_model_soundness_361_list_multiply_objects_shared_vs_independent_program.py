# `[[]] * n` shares references in CPython — model copies (over-proves
# independence); must reject list-multiply with mutable elements
"""
LIST MULTIPLY WITH OBJECTS — CPython SHARES REFERENCES, MODEL COPIES

CPython: [[0]] * 3 → [[0], [0], [0]] — all THREE inner lists are the
         SAME OBJECT. Modifying one modifies all:
         xs = [[0]] * 3; xs[0][0] = 99 → [[99], [99], [99]]

Model:   List_repeat creates independent copies (value semantics).
         xs[0][0] = 99 → [[99], [0], [0]] — only first modified.

         For PRIMITIVE elements ([0] * 3 → [0, 0, 0]), value semantics
         is CORRECT (ints are immutable, no aliasing observable).

         For OBJECT elements, value semantics OVER-PROVES independence:
         the model says elements are independent when CPython says they're
         aliased. This is a FALSE NEGATIVE — the model misses a bug class
         where mutation through one reference affects others.

The subset bans aliasing, so this pattern SHOULD be rejected.
But the AST checker must detect `[mutable] * n` as creating aliases.
"""
from dataclasses import dataclass


@dataclass
class Cell:
    value: int


def primitive_repeat() -> list[int]:
    """Primitive repeat — value semantics is CORRECT here."""
    xs: list[int] = [0] * 5
    xs[0] = 99
    # CPython: [99, 0, 0, 0, 0] — ints are immutable, no aliasing
    # Model: same result (correct for primitives)
    return xs


def object_repeat_bug() -> list[list[int]]:
    """Object repeat — CPython shares references, model doesn't."""
    # This creates aliased inner lists in CPython
    rows: list[list[int]] = [[0, 0, 0]] * 3
    rows[0][0] = 99
    # CPython: [[99,0,0], [99,0,0], [99,0,0]] — ALL rows modified!
    # Model: [[99,0,0], [0,0,0], [0,0,0]] — only first row modified
    return rows


def correct_pattern() -> list[list[int]]:
    """Correct way to create independent rows."""
    rows: list[list[int]] = []
    i: int = 0
    while i < 3:
        rows.append([0, 0, 0])  # fresh list each iteration
        i += 1
    rows[0][0] = 99
    # CPython: [[99,0,0], [0,0,0], [0,0,0]] — independent
    # Model: same (correct)
    return rows


def main() -> None:
    # Test 1: primitive repeat (both correct)
    p: list[int] = primitive_repeat()
    assert p == [99, 0, 0, 0, 0]

    # Test 2: object repeat (divergence!)
    buggy: list[list[int]] = object_repeat_bug()
    # CPython: all rows are [99,0,0] due to aliasing
    assert buggy[0] == [99, 0, 0]
    assert buggy[1] == [99, 0, 0]  # aliased!
    assert buggy[2] == [99, 0, 0]  # aliased!

    # Test 3: correct pattern (both agree)
    correct: list[list[int]] = correct_pattern()
    assert correct[0] == [99, 0, 0]
    assert correct[1] == [0, 0, 0]  # independent
    assert correct[2] == [0, 0, 0]  # independent

    print("all passed")


main()
