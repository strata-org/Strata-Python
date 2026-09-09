# Test: while isinstance(obj.x, int) + method mutation mid-body.
"""Test: while isinstance(obj.x, int) + method mutation mid-body."""


class Counter:
    def __init__(self) -> None:
        self.x: int | str = 10

    def decrement(self) -> None:
        if isinstance(self.x, int) and self.x <= 0:
            self.x = "done"


def main() -> None:
    c = Counter()
    while isinstance(c.x, int):
        c.decrement()  # may change c.x to "done"
        # mypy: c.x is int (from while condition narrowing)
        # Runtime: c.x could be "done" (str) after decrement
        result: int = c.x - 1  # TypeError if c.x is now str


if __name__ == "__main__":
    main()
