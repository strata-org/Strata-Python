# isinstance narrows `obj.x` to int. A method call inside `try` mutates
# `obj.x` to str AND raises an exception. In the `except` handler, mypy still
# has the isinstance narrowing active, but the mutation happened before the
# raise.
"""
a21_exception_handler_narrowing.py — Narrowing persists into except handler after mutation.

isinstance narrows obj.x to int. A method call raises AND mutates obj.x.
In the except handler, mypy still has the narrowing active, but obj.x is now str.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Fragile:
    def __init__(self) -> None:
        self.x: int | str = 42

    def fail_and_mutate(self) -> None:
        self.x = "broken"
        raise ValueError("oops")


def main() -> None:
    f = Fragile()
    if isinstance(f.x, int):
        try:
            f.fail_and_mutate()  # mutates f.x to str, then raises
        except ValueError:
            # mypy: f.x is still int (narrowing from isinstance)
            # Runtime: f.x is "broken" (str)
            result: int = f.x - 1  # TypeError


if __name__ == "__main__":
    main()
