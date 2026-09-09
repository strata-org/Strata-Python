# isinstance narrows `obj.x` to int. Assigning to `obj.y` triggers `@y.setter`
# which mutates `obj.x` to str. Mypy treats `obj.y = 5` as a simple attribute
# assignment and does NOT invalidate narrowing on `obj.x`.
"""
a32_property_setter_side_effect.py — @property setter mutates a DIFFERENT narrowed field.

isinstance narrows obj.x to int. Assigning to obj.y triggers @y.setter which
mutates obj.x to str. mypy sees `obj.y = 5` as a plain attribute assignment
and doesn't invalidate narrowing on obj.x.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Tricky:
    def __init__(self) -> None:
        self.x: int | str = 42
        self._y: int = 0

    @property
    def y(self) -> int:
        return self._y

    @y.setter
    def y(self, val: int) -> None:
        self._y = val
        self.x = "side effect"  # mutates x!


def main() -> None:
    t = Tricky()
    if isinstance(t.x, int):
        t.y = 5  # mypy: simple assignment. Runtime: triggers setter, mutates t.x
        result: int = t.x - 1  # mypy: int. Runtime: str - int → TypeError


if __name__ == "__main__":
    main()
