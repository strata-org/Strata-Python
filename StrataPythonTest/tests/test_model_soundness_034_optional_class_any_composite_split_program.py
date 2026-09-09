# `Optional[MyClass]` spans Any/Composite split — if classes move to Composite
# for heap semantics, `None | MyClass` is unrepresentable
"""
Optional[MyClass] means the variable can be None or a MyClass instance.
The Any datatype has from_None but class instances use from_ClassInstance
(or Composite). If the translator uses Composite for classes, then
Optional[MyClass] spans two representation worlds (Any for None, Composite
for the class) with no coercion path between them.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Node:
    value: int
    next: Optional["Node"]


def list_sum(head: Optional[Node]) -> int:
    total: int = 0
    current: Optional[Node] = head
    while current is not None:
        total = total + current.value
        current = current.next
    return total


def find(head: Optional[Node], target: int) -> bool:
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

    s: int = list_sum(n1)
    assert s == 6

    assert find(n1, 2) == True
    assert find(n1, 5) == False

    print(s, find(n1, 2), find(n1, 5))


main()
