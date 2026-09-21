# A ghost's `type=` may name a TypedDict alias declared before it.
from typing import TypedDict

Item = TypedDict('Item', {'k': str})
ghost(name="pending", type=Item)
