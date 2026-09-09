# isinstance narrows `obj.x` to int. Inside a `try` block, a `finally` clause
# calls a method that mutates `obj.x` to str. Code **after** the try/finally
# statement still has the isinstance narrowing active per mypy, but the
# finally block always executes and changes the type.
"""
a18_finally_mutation.py — finally block mutates narrowed field; code after try uses stale narrowing.

isinstance narrows obj.x to int inside try. The finally block always runs and
mutates obj.x to str. Code AFTER the try/finally still has the narrowing active
per mypy, but the field is now str.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


class Resource:
    def __init__(self) -> None:
        self.x: int | str = 42

    def cleanup(self) -> None:
        self.x = "cleaned"


def main() -> None:
    r = Resource()
    if isinstance(r.x, int):
        try:
            pass
        finally:
            r.cleanup()  # mutates r.x to "cleaned" (str)
        # mypy: r.x is still int (narrowing from isinstance persists past finally)
        result: int = r.x - 1  # TypeError: str - int


if __name__ == "__main__":
    main()
