# When does class become Composite — decision boundary: functional style →
# ClassInstance; imperative mutation → Composite; v1 subset = always
# ClassInstance
"""
The `Any` datatype has BOTH `from_ClassInstance` (value) and
`from_Composite` (heap). The translator must decide which to use.

Decision criteria:
- If the class is NEVER aliased and methods return new instances → ClassInstance
- If the class IS aliased or methods mutate in place → Composite

For the Frontend v1 subset (no aliasing), ALL classes use ClassInstance.
But what if a class is used in a way that LOOKS like it needs Composite
but is actually fine under value semantics?

This finding tests the BOUNDARY: patterns that work under value semantics
but might be mistakenly flagged as needing Composite.

Key insight: if the programmer follows the functional pattern (return new
instances, rebind at caller), value semantics is ALWAYS correct. The
Composite encoding is only needed for IMPERATIVE patterns (mutate in place,
aliasing visible to caller).

Uses ONLY confirmed-accepted constructs: @dataclass, method, int, list.
"""
from dataclasses import dataclass


@dataclass
class Stack:
    """Stack using functional style — ClassInstance is correct."""
    items: list[int]
    size: int

    def push(self: "Stack", val: int) -> "Stack":
        new_items: list[int] = self.items + [val]
        return Stack(items=new_items, size=self.size + 1)

    def pop(self: "Stack") -> "Stack":
        if self.size == 0:
            return self
        new_items: list[int] = self.items[:-1] if self.size > 1 else []
        return Stack(items=new_items, size=self.size - 1)

    def peek(self: "Stack") -> int:
        return self.items[self.size - 1]

    def is_empty(self: "Stack") -> bool:
        return self.size == 0


def functional_stack_usage() -> int:
    """Stack with functional pattern — value semantics correct."""
    s: Stack = Stack(items=[], size=0)
    s = s.push(10)
    s = s.push(20)
    s = s.push(30)
    # s.items = [10, 20, 30], s.size = 3
    top: int = s.peek()  # 30
    s = s.pop()
    # s.items = [10, 20], s.size = 2
    return top + s.peek()  # 30 + 20 = 50


def multiple_stacks_independent() -> bool:
    """Two stacks are independent — value semantics correct."""
    s1: Stack = Stack(items=[], size=0)
    s2: Stack = Stack(items=[], size=0)

    s1 = s1.push(1)
    s1 = s1.push(2)
    s2 = s2.push(99)

    return s1.size == 2 and s2.size == 1 and s1.peek() == 2 and s2.peek() == 99


def stack_snapshot() -> bool:
    """Taking a 'snapshot' by not rebinding — value semantics makes this free."""
    s: Stack = Stack(items=[], size=0)
    s = s.push(1)
    s = s.push(2)

    snapshot: Stack = s  # Under value semantics: independent copy
    # Under Composite: this would be an alias!

    s = s.push(3)
    # snapshot is unchanged (value semantics)
    # Under Composite with aliasing: snapshot.size would be 3 (WRONG for snapshot)
    return snapshot.size == 2 and s.size == 3


def main() -> None:
    assert functional_stack_usage() == 50
    assert multiple_stacks_independent() == True
    assert stack_snapshot() == True

    print(functional_stack_usage(), multiple_stacks_independent(),
          stack_snapshot())


main()
