# Method calling another method on self — `self.add(self.value)` must evaluate
# arg first, then dispatch; method on result vs self
"""
A method calling another method on self. Under value semantics, `self`
is a ClassInstance value. Calling `self.other_method()` must pass the
CURRENT self (with any field updates from earlier in the method).

All constructs used: @dataclass, method def, self.method(), int.
Frontend accepts this — no unsupported construct.
"""
from dataclasses import dataclass


@dataclass
class Calculator:
    value: int

    def add(self: "Calculator", n: int) -> "Calculator":
        return Calculator(value=self.value + n)

    def double(self: "Calculator") -> "Calculator":
        return self.add(self.value)  # calls self.add

    def square(self: "Calculator") -> "Calculator":
        return Calculator(value=self.value * self.value)

    def add_and_double(self: "Calculator", n: int) -> "Calculator":
        """Chain: add n, then double."""
        result: Calculator = self.add(n)
        return result.double()

    def get(self: "Calculator") -> int:
        return self.value


def method_calls_method() -> int:
    c: Calculator = Calculator(value=5)
    c = c.double()  # double calls add(5) → value = 10
    return c.get()


def chained_internal() -> int:
    c: Calculator = Calculator(value=3)
    c = c.add_and_double(2)  # add(2)→5, double→10
    return c.get()


def multiple_self_calls() -> int:
    c: Calculator = Calculator(value=2)
    c = c.add(3)     # 5
    c = c.double()   # 10
    c = c.add(1)     # 11
    return c.get()


def main() -> None:
    assert method_calls_method() == 10
    assert chained_internal() == 10
    assert multiple_self_calls() == 11

    print(method_calls_method(), chained_internal(), multiple_self_calls())


main()
