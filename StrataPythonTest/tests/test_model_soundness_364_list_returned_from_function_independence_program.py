# List returned from accessor creates alias — `return self.items` gives
# reference in CPython, copy in model; must reject or use heap
"""
LIST RETURNED FROM FUNCTION — CALLER AND CALLEE INDEPENDENT (POSITIVE)

CPython: def make_list(): return [1,2,3]
         a = make_list(); b = make_list()
         a.append(4)
         b == [1,2,3]  # True — each call returns a fresh list

Model:   Value semantics: each function call returns an independent value.
         Modifying a doesn't affect b. This is CORRECT.

         BUT: def get_shared(): return self.items
         a = obj.get_items(); a.append(4)
         In CPython: obj.items is NOW [1,2,3,4] (aliased!)
         In Model: obj.items is still [1,2,3] (value copy)

         The model is CORRECT for factory functions (returning new lists)
         but WRONG for accessor functions (returning references to existing lists).

This finding confirms value semantics is SOUND for the factory pattern
but UNSOUND for the accessor pattern. The AST checker must distinguish them.
"""
from dataclasses import dataclass


def make_list() -> list[int]:
    """Factory: returns a fresh list each time."""
    return [1, 2, 3]


def make_range(n: int) -> list[int]:
    """Factory: builds and returns a new list."""
    result: list[int] = []
    i: int = 0
    while i < n:
        result.append(i)
        i += 1
    return result


@dataclass
class Container:
    items: list[int]

    def get_items(self: "Container") -> list[int]:
        """Accessor: returns reference to internal list."""
        return self.items


def test_factory_independence() -> bool:
    """Two calls to factory produce independent lists."""
    a: list[int] = make_list()
    b: list[int] = make_list()
    a.append(4)
    # CPython: b is still [1,2,3] — independent (fresh allocation each call)
    # Model: same — value semantics gives independence
    return b == [1, 2, 3]


def test_accessor_aliasing() -> bool:
    """Accessor returns reference — mutation visible through original."""
    c: Container = Container([1, 2, 3])
    items: list[int] = c.get_items()
    items.append(4)
    # CPython: c.items is now [1,2,3,4] — items is alias to c.items
    # Model: c.items is still [1,2,3] — value copy, no aliasing
    # DIVERGENCE: model says len(c.items)==3, CPython says 4
    return len(c.items) == 4


def main() -> None:
    # Test 1: factory independence (BOTH CORRECT)
    assert test_factory_independence()

    # Test 2: accessor aliasing (DIVERGENCE)
    # CPython: True (mutation visible through original)
    # Model: False (value copy, mutation invisible)
    assert test_accessor_aliasing()

    print("all passed")


main()
