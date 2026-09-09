# `list[MyClass]` stores `from_Composite(ref)` in ListAny — coercion path
# between value-list and heap-objects
"""
A `list[MyClass]` stores objects in a list. If MyClass uses Composite
(heap semantics), the list stores Composite REFERENCES (not values).
But ListAny stores `Any` values. To put a Composite reference in a
ListAny, it must be wrapped as `from_Composite(ref)`.

This means list operations must handle the wrapping/unwrapping:
- Storing: wrap Composite ref as from_Composite before List_append
- Loading: unwrap from_Composite after List_get to access heap fields
- The list itself remains value-semantics (ListAny), but its ELEMENTS
  are heap references

This is the coercion path between the two worlds.
"""
from dataclasses import dataclass


@dataclass
class Item:
    name: str
    price: int


def find_cheapest(items: list[Item]) -> Item:
    best: Item = items[0]
    i: int = 1
    while i < len(items):
        if items[i].price < best.price:
            best = items[i]
        i = i + 1
    return best


def total_price(items: list[Item]) -> int:
    total: int = 0
    for item in items:
        total = total + item.price
    return total


def apply_discount(items: list[Item], pct: int) -> None:
    """Modify each item's price in place."""
    i: int = 0
    while i < len(items):
        items[i].price = items[i].price * (100 - pct) // 100
        i = i + 1


def main() -> None:
    inventory: list[Item] = [
        Item(name="apple", price=100),
        Item(name="banana", price=50),
        Item(name="cherry", price=200),
    ]

    # Find cheapest
    cheap: Item = find_cheapest(inventory)
    assert cheap.name == "banana"
    assert cheap.price == 50

    # Total
    assert total_price(inventory) == 350

    # Discount modifies items in place
    apply_discount(inventory, 10)  # 10% off
    assert inventory[0].price == 90   # 100 * 90 / 100
    assert inventory[1].price == 45   # 50 * 90 / 100
    assert inventory[2].price == 180  # 200 * 90 / 100

    print(cheap.name, total_price(inventory))


main()
