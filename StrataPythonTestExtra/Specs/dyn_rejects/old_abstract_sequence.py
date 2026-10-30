from typing import Sequence, Any

@admit(lambda xs, result: len(xs) == OLD(len(xs)) + 1)
def grow(xs: Sequence[Any]) -> None:
    ...
