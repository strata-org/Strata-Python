# Recursive dataclass with `Optional[Self]` field — type-level reasoning and
# loop termination for recursive traversal
"""
A dataclass with an Optional self-referential field creates a recursive
type: `Optional[Node]` means the field is either None or another Node.
The Laurel `from_ClassInstance` encoding stores attributes in a flat
DictStrAny. A recursive structure (linked list, tree) requires that
the DictStrAny can contain `from_ClassInstance` values — which it can,
since values are `Any`. But the model may not handle:
1. Traversal termination (checking `node.next is None` to stop)
2. Depth-dependent properties (the type is infinitely recursive)
3. Construction of nested instances
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Node:
    value: int
    next: Optional["Node"]


def list_sum(head: Optional[Node]) -> int:
    """Sum all values in a linked list."""
    total: int = 0
    current: Optional[Node] = head
    while current is not None:
        total = total + current.value
        current = current.next
    return total


def list_length(head: Optional[Node]) -> int:
    """Count nodes in a linked list."""
    count: int = 0
    current: Optional[Node] = head
    while current is not None:
        count = count + 1
        current = current.next
    return count


def find_value(head: Optional[Node], target: int) -> bool:
    """Check if target exists in the list."""
    current: Optional[Node] = head
    while current is not None:
        if current.value == target:
            return True
        current = current.next
    return False


def main() -> None:
    # Build a linked list: 1 -> 2 -> 3 -> None
    n3: Node = Node(value=3, next=None)
    n2: Node = Node(value=2, next=n3)
    n1: Node = Node(value=1, next=n2)

    # Traverse and sum
    s: int = list_sum(n1)
    # CPython: 1 + 2 + 3 = 6
    assert s == 6

    # Length
    l: int = list_length(n1)
    assert l == 3

    # Find
    assert find_value(n1, 2) == True
    assert find_value(n1, 5) == False

    # Empty list
    assert list_sum(None) == 0
    assert list_length(None) == 0

    # Single element
    single: Node = Node(value=42, next=None)
    assert list_sum(single) == 42
    assert list_length(single) == 1

    print(s, l, find_value(n1, 2))


main()
