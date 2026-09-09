# isinstance narrowing on `self.value: int|str` not invalidated after
# `self.to_str()` mutates the field to str.
"""
a1_narrowing_method.py — isinstance narrowing invalidated by direct method call.

mypy --strict: Success (0 errors)
Runtime: AssertionError — variable is str where mypy says int
"""

class Cell:
    def __init__(self, value: int | str) -> None:
        self.value: int | str = value

    def to_str(self) -> None:
        self.value = "hello"

def main() -> None:
    c = Cell(42)
    if isinstance(c.value, int):
        c.to_str()  # mutates c.value from int to str
        x: int = c.value - 1  # mypy: int - int. Runtime: str - int → TypeError

if __name__ == "__main__":
    main()
