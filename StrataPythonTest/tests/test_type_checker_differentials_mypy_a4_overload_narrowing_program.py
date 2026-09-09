# @overload selects wrong branch because narrowing is stale: mypy picks
# `process(int) -> int` but runtime value is str.
"""
a4_overload_narrowing.py — overloaded function + narrowing invalidation.

Combines narrowing invalidation with @overload: mypy selects the int→int
overload based on the narrowed type, but the actual runtime value is str.

mypy --strict: Success (0 errors)
Runtime: AssertionError — got str where mypy inferred int (from overload resolution)
"""
from typing import overload

@overload
def process(x: int) -> int: ...
@overload
def process(x: str) -> str: ...

def process(x: int | str) -> int | str:
    if isinstance(x, int):
        return x + 1
    return x.upper()

class Tricky:
    def __init__(self) -> None:
        self.val: int | str = 42

    def flip(self) -> None:
        if isinstance(self.val, int):
            self.val = "flipped"
        else:
            self.val = 0

def main() -> None:
    t = Tricky()
    if isinstance(t.val, int):
        t.flip()  # changes t.val to "flipped" (str)
        # mypy thinks t.val is int → selects process(int) → int overload
        result: int = process(t.val)
        result2: int = result - 1  # mypy: int - int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
