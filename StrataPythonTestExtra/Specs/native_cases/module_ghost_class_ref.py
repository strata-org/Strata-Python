# A ghost's `type=` may name a user-declared class defined before it.
class Item:
    k: str


ghost(name="pending", type=Item)
