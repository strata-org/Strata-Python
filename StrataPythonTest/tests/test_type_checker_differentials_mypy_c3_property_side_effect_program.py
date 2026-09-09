# @property getter has side effect: changes internal state so second access
# returns different type.
"""
c3_property_side_effect.py — isinstance narrowing on property invalidated by re-access.

The property has a side effect: it changes the underlying value on second access.
mypy narrows based on the first access, but the second access returns a different type.

No explicit mutation call. The narrowing is invalidated by the SAME expression
being evaluated twice (isinstance check + subsequent use).

mypy --strict: Success (0 errors)
Runtime: AssertionError — variable is str where mypy says int
"""

class Sneaky:
    def __init__(self) -> None:
        self._val: int | str = 42
        self._count: int = 0

    @property
    def val(self) -> int | str:
        self._count += 1
        if self._count > 1:
            self._val = "switched"
        return self._val

def main() -> None:
    s = Sneaky()
    if isinstance(s.val, int):  # first access: returns 42 (int), count → 1
        x: int = s.val - 1  # second access returns str. str - int → TypeError

if __name__ == "__main__":
    main()
