# match/case narrowing not invalidated by method call inside the case branch.
"""
a6_match_narrowing.py — match statement narrowing invalidated by method call.

Same mechanism as isinstance narrowing (Category A) but through Python 3.10+
match/case syntax. Demonstrates that the structural pattern matching has the
same unsoundness as isinstance.

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""

class Tagged:
    def __init__(self) -> None:
        self.tag: int | str = 1

    def flip(self) -> None:
        self.tag = "flipped"

def main() -> None:
    t = Tagged()
    match t.tag:
        case int():
            t.flip()  # mutates t.tag to str
            result: int = t.tag - 1  # mypy: int (match narrowed). Runtime: TypeError

if __name__ == "__main__":
    main()
