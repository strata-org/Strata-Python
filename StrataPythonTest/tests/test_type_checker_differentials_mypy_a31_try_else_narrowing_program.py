# isinstance narrows `obj.x` to int. In the `try` body, a method mutates
# `obj.x` to str without raising. The `else` clause (which runs only when no
# exception occurred) still has the narrowing active per mypy. But the method
# already changed the type.
"""
a31_try_else_narrowing.py — try/else: method mutates in try body without raising,
else clause uses stale narrowing.

isinstance narrows obj.x to int. In the try body, a method mutates obj.x to str
but does NOT raise. The else clause (runs when no exception) still has the
narrowing active per mypy.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Worker:
    def __init__(self) -> None:
        self.x: int | str = 42

    def process(self) -> None:
        self.x = "done"  # mutates without raising


def main() -> None:
    w = Worker()
    if isinstance(w.x, int):
        try:
            w.process()  # mutates w.x to "done", no exception
        except ValueError:
            pass
        else:
            # Runs because process() didn't raise
            # mypy: w.x is int (narrowing persists into else)
            # Runtime: w.x is "done" (str)
            result: int = w.x - 1  # TypeError


if __name__ == "__main__":
    main()
