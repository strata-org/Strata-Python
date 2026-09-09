# Multiple fields narrowed independently; a single method call corrupts both.
# Using both in one expression (`p.a - p.b`) produces TypeError.
"""
a12_multiple_fields.py — Multiple fields narrowed, single call corrupts both.

Z3-predicted: mypy narrows x.a and x.b independently. A single method call
that changes BOTH is not detected because mypy only invalidates on direct
assignment to the specific expression, not on arbitrary method calls.

The exploit uses both corrupted fields in a single expression (a - b)
which produces TypeError (str - str is not supported).

mypy --strict: Success (0 errors)
Runtime: TypeError — unsupported operand type(s) for -: 'str' and 'str'
"""

class Pair:
    def __init__(self) -> None:
        self.a: int | str = 1
        self.b: int | str = 2

    def corrupt_both(self) -> None:
        self.a = "x"
        self.b = "y"

def main() -> None:
    p = Pair()
    if isinstance(p.a, int) and isinstance(p.b, int):
        p.corrupt_both()  # changes both to str
        # mypy: p.a is int AND p.b is int (both narrowings active)
        result: int = p.a - p.b  # str - str → TypeError

if __name__ == "__main__":
    main()
