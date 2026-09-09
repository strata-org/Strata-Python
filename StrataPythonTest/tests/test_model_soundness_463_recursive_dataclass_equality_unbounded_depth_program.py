# Recursive @dataclass equality — `Node(1, Node(2, None)) == Node(1, Node(2,
# None))` requires unbounded-depth PEq recursion; SMT solver can't unroll;
# Unknown or Hole
"""
RECURSIVE DATACLASS EQUALITY REQUIRES UNBOUNDED-DEPTH PEQ RECURSION

The subset allows:
  - @dataclass with Optional[Self] field (IN, finding 067)
  - @dataclass structural equality (IN, finding 213)
  - Equality comparison == (IN)

The NOVEL gap: @dataclass generates __eq__ that compares field-by-field.
When a field is itself a @dataclass (or Optional[@dataclass]), equality
must RECURSE into that field. For recursive structures like linked lists,
this recursion is unbounded.

  @dataclass
  class Node:
      value: int
      next: Optional["Node"]

  a = Node(1, Node(2, Node(3, None)))
  b = Node(1, Node(2, Node(3, None)))
  a == b  # True — requires comparing 3 levels deep

The model's PEq on ClassInstance compares:
  1. classname strings (equal: "Node" == "Node")
  2. instance_attributes DictStrAny (structural comparison)

But DictStrAny structural comparison on the "next" field encounters
ANOTHER from_ClassInstance value, requiring PEq to call itself recursively.

ROOT CAUSE: PEq is likely defined as a FLAT function that compares
DictStrAny entries with a single level of PEq. It has no recursive
case for from_ClassInstance values nested inside DictStrAny.

Even if PEq IS recursive, the SMT solver cannot unroll it to arbitrary
depth. For a linked list of length N, the solver needs N recursive
unrollings of PEq — which is unbounded.

CPython: True (recursive __eq__ terminates because structure is finite)
Model: Either Hole (no recursive case) or Unknown (solver timeout)

This affects ALL recursive data structures: linked lists, trees,
expression ASTs — any @dataclass with Optional[Self] fields.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class Node:
    value: int
    next: Optional["Node"]


def build_list(n: int) -> Optional[Node]:
    """Build a linked list 1 -> 2 -> ... -> n -> None."""
    result: Optional[Node] = None
    i: int = n
    while i > 0:
        result = Node(value=i, next=result)
        i = i - 1
    return result


def lists_equal(a: Optional[Node], b: Optional[Node]) -> bool:
    """Manual iterative equality (workaround for recursive __eq__)."""
    ca: Optional[Node] = a
    cb: Optional[Node] = b
    while ca is not None and cb is not None:
        if ca.value != cb.value:
            return False
        ca = ca.next
        cb = cb.next
    return ca is None and cb is None


def test_shallow_equality() -> bool:
    """Depth-1: single node. PEq may handle this."""
    a: Node = Node(value=42, next=None)
    b: Node = Node(value=42, next=None)
    return a == b  # True: same value, both next=None


def test_depth_two_equality() -> bool:
    """Depth-2: PEq must recurse once into the 'next' field."""
    a: Node = Node(value=1, next=Node(value=2, next=None))
    b: Node = Node(value=1, next=Node(value=2, next=None))
    return a == b  # True: requires recursive comparison


def test_depth_three_inequality() -> bool:
    """Depth-3 with difference at leaf: requires full traversal."""
    a: Node = Node(value=1, next=Node(value=2, next=Node(value=3, next=None)))
    b: Node = Node(value=1, next=Node(value=2, next=Node(value=99, next=None)))
    return a != b  # True: differ at depth 3


def test_length_mismatch() -> bool:
    """Different lengths: one list longer than other."""
    a: Node = Node(value=1, next=Node(value=2, next=None))
    b: Node = Node(value=1, next=None)
    return a != b  # True: b.next is None, a.next is Node


def main() -> None:
    assert test_shallow_equality()
    assert test_depth_two_equality()
    assert test_depth_three_inequality()
    assert test_length_mismatch()

    # Build and compare equal lists
    list_a: Optional[Node] = build_list(5)
    list_b: Optional[Node] = build_list(5)
    assert list_a == list_b  # Requires depth-5 recursive PEq

    # Manual equality matches == operator
    assert lists_equal(list_a, list_b) == (list_a == list_b)

    print("all passed")


main()
