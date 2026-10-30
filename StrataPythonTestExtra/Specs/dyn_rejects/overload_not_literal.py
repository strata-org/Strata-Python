# An overload that doesn't dispatch on a string literal rejects the model.
from typing import overload

@overload
def connect(name: str) -> int:
    ...
