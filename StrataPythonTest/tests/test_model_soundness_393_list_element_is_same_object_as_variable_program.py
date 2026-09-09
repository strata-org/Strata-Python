# List element same as local variable — reassignment breaks alias in BOTH
# CPython and model; POSITIVE confirmation of value semantics
"""
LIST ELEMENT IS SAME OBJECT AS LOCAL VARIABLE — ALIAS THROUGH CONTAINER

CPython: obj = Point(1, 2); lst = [obj]
         obj.x = 99 → lst[0].x is also 99 (same object!)

Model:   lst = [copy_of_obj]
         Modifying obj doesn't affect lst[0] (independent copy)

Under functional style (reassignment):
         obj = Point(99, 2)  → lst[0] is still Point(1, 2)
         This is CORRECT in both CPython and model!

         CPython: obj now points to NEW object; lst[0] still points to OLD
         Model: obj is new value; lst[0] is independent copy of old value

The key insight: REASSIGNMENT (obj = new_value) breaks the alias in
CPython too! Only IN-PLACE MUTATION (obj.x = 99) shows the difference.
Since the subset uses functional style, this is SOUND.
"""
from dataclasses import dataclass


@dataclass
class Item:
    name: str
    count: int


def variable_and_list_element() -> bool:
    """Variable and list element — reassignment breaks alias in both models."""
    item: Item = Item("apple", 5)
    basket: list[Item] = [item]

    # Reassign variable (NOT in-place mutation)
    item = Item("apple", 10)

    # CPython: basket[0] still has count=5 (item now points elsewhere)
    # Model: basket[0] is independent copy with count=5
    # BOTH AGREE: basket[0].count == 5
    return basket[0].count == 5


def build_list_then_reassign_source() -> bool:
    """Build list from variable, then reassign variable."""
    a: Item = Item("x", 1)
    b: Item = Item("y", 2)
    items: list[Item] = [a, b]

    # Reassign a — list element unchanged
    a = Item("x", 99)

    return items[0].count == 1 and items[1].count == 2


def function_modifies_local_not_list() -> bool:
    """Function receives item from list, reassigns locally."""
    items: list[Item] = [Item("a", 1), Item("b", 2)]

    # Extract element, modify locally
    first: Item = items[0]
    first = Item(first.name, first.count + 10)

    # List element unchanged (reassignment, not mutation)
    return items[0].count == 1 and first.count == 11


def main() -> None:
    assert variable_and_list_element()
    assert build_list_then_reassign_source()
    assert function_modifies_local_not_list()

    print("all passed")


main()
