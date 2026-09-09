# Python evaluates binary expressions left-to-right. In `obj.method() +
# obj.x`, `obj.method()` executes first (mutating `obj.x` to str), then
# `obj.x` is read (now str). The result is `int + str → TypeError`.
"""
a17_expression_eval_order.py — Evaluation order within a single expression invalidates narrowing.

obj.x narrowed to int. In the expression `obj.method() + obj.x`, Python evaluates
left-to-right: obj.method() runs first (mutates obj.x to str), then obj.x is read.
Result: int + str → TypeError.

mypy --strict: Success (0 errors)
Runtime: TypeError — unsupported operand type(s) for +: 'int' and 'str'
"""


class Expr:
    def __init__(self) -> None:
        self.x: int | str = 10

    def get_and_mutate(self) -> int:
        self.x = "mutated"
        return 5


def main() -> None:
    e = Expr()
    if isinstance(e.x, int):
        # Python eval order: e.get_and_mutate() first, then e.x
        # After get_and_mutate runs, e.x is "mutated" (str)
        # So this is: 5 + "mutated" → TypeError
        result: int = e.get_and_mutate() + e.x


if __name__ == "__main__":
    main()
