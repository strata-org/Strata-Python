# Value sem: list in object field stale — `bag.items.append(x)` reads copy,
# appends to copy, discards; bag.items unchanged
"""
VALUE SEMANTICS WHERE CPYTHON HAS REFERENCE SEMANTICS:
List stored in object field — modifying the list through the field
is visible in CPython but lost in the model.

CPython: obj.items is a reference to the list. obj.items.append(x)
         mutates the list. Reading obj.items later sees the change.
Model: obj.items is a COPY of the list stored in the attrs dict.
       Appending to it creates a new list but doesn't update the object.

CPython result: len(bag.items) == 3
Model result:  len(bag.items) == 0 (or stale copy)
"""
from dataclasses import dataclass


@dataclass
class Bag:
    items: list[int]

    def add(self: "Bag", item: int) -> "Bag":
        """Correct pattern: return new Bag with updated items."""
        new_items: list[int] = self.items + [item]
        return Bag(items=new_items)


def wrong_pattern() -> int:
    """WRONG: mutate field's list directly. Diverges."""
    bag: Bag = Bag(items=[])
    bag.items.append(1)  # CPython: mutates the list IN the bag
                         # Model: reads copy, appends to copy, discards
    bag.items.append(2)
    bag.items.append(3)
    return len(bag.items)  # CPython: 3. Model: 0 (original empty list)


def correct_pattern() -> int:
    """CORRECT: use functional method that returns new Bag."""
    bag: Bag = Bag(items=[])
    bag = bag.add(1)
    bag = bag.add(2)
    bag = bag.add(3)
    return len(bag.items)  # 3 in BOTH


def main() -> None:
    # Wrong pattern: diverges
    assert wrong_pattern() == 3  # True in CPython

    # Correct pattern: works in both
    assert correct_pattern() == 3

    print(wrong_pattern(), correct_pattern())


main()
