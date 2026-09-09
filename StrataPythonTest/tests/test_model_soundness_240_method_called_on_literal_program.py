# Method called on literal/constructor — `"hello".upper()`,
# `Point(3,4).norm()` need ANF: lift non-variable receiver to temporary
"""
Calling a method on a LITERAL or constructor expression:
    [1, 2, 3].append(4)   — method on list literal
    "hello".upper()       — method on string literal
    Point(1, 2).norm()    — method on constructor result

The model must handle method calls where the receiver is NOT a variable
but an expression. Finding 159 covered chaining. This finding covers
the base case: method on a literal/constructor.

The result of the method call is a value. If the method mutates (append),
the mutation is lost (no variable to rebind). If the method is pure
(upper, norm), the result is usable.

Uses ONLY confirmed-accepted constructs: str methods, list, @dataclass.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int

    def norm_sq(self: "Point") -> int:
        return self.x * self.x + self.y * self.y

    def translate(self: "Point", dx: int, dy: int) -> "Point":
        return Point(x=self.x + dx, y=self.y + dy)


def method_on_string_literal() -> str:
    return "hello".upper()  # "HELLO"


def method_on_constructor() -> int:
    return Point(3, 4).norm_sq()  # 25


def chained_on_constructor() -> int:
    return Point(0, 0).translate(3, 4).norm_sq()  # 25


def method_on_list_result() -> int:
    """len() on a list expression."""
    return len([1, 2, 3] + [4, 5])  # 5


def string_method_chain() -> str:
    return "  Hello World  ".strip().lower()  # "hello world"


def main() -> None:
    assert method_on_string_literal() == "HELLO"
    assert method_on_constructor() == 25
    assert chained_on_constructor() == 25
    assert method_on_list_result() == 5
    assert string_method_chain() == "hello world"

    print(method_on_string_literal(), method_on_constructor(),
          string_method_chain())


main()
