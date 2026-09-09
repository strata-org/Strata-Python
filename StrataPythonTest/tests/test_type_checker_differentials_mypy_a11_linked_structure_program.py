# Mutation through a linked data structure: `b.next.val = 'corrupted'` changes
# `a.val` because `b.next is a`.
"""
a11_linked_structure.py — Mutation through a linked data structure.

Object A's field is narrowed to int. Object B holds a reference to A.
Mutating through B.next.val changes A.val without mypy seeing it.

This is distinct from a3 (indirect reference chain on SAME object).
Here we have TWO separate objects where one holds a pointer to the other.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""
from __future__ import annotations

class Node:
    def __init__(self, val: int | str, next: Node | None = None) -> None:
        self.val: int | str = val
        self.next: Node | None = next

    def corrupt_next(self) -> None:
        if self.next is not None:
            self.next.val = "corrupted"

def main() -> None:
    a = Node(1)
    b = Node(2, a)  # b.next points to a
    if isinstance(a.val, int):
        b.corrupt_next()  # sets b.next.val = "corrupted", i.e., a.val = "corrupted"
        result: int = a.val - 1  # mypy: int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
