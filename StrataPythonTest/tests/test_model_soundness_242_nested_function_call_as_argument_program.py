# Nested function calls as arguments — `f(g(x), h(y))` requires ANF: evaluate
# inner calls to temps before outer call
"""
Nested function calls as arguments: `f(g(x), h(y))`.
The model must:
1. Evaluate g(x) first → result1
2. Evaluate h(y) second → result2
3. Call f(result1, result2)

Evaluation order is left-to-right (finding 132). Each intermediate
result must be available as input to the outer call.

This is the ANF requirement (finding 159/240) applied to function
arguments: each argument expression must be evaluated to a temporary
before the outer call.

Uses ONLY Frontend-subset features: function def, int, nested calls.
"""


def double(x: int) -> int:
    return x * 2


def add_one(x: int) -> int:
    return x + 1


def add(a: int, b: int) -> int:
    return a + b


def nested_simple() -> int:
    """f(g(x)) — one level of nesting."""
    return double(add_one(5))  # add_one(5)=6, double(6)=12


def nested_two_args() -> int:
    """f(g(x), h(y)) — two nested calls as arguments."""
    return add(double(3), add_one(4))  # double(3)=6, add_one(4)=5, add(6,5)=11


def deeply_nested() -> int:
    """f(g(h(x))) — three levels."""
    return double(double(add_one(2)))  # add_one(2)=3, double(3)=6, double(6)=12


def nested_with_literal() -> int:
    """Mix of nested calls and literals."""
    return add(double(5), 3)  # double(5)=10, add(10,3)=13


def nested_same_function() -> int:
    """add(add(1,2), add(3,4)) — same function nested."""
    return add(add(1, 2), add(3, 4))  # add(1,2)=3, add(3,4)=7, add(3,7)=10


def main() -> None:
    assert nested_simple() == 12
    assert nested_two_args() == 11
    assert deeply_nested() == 12
    assert nested_with_literal() == 13
    assert nested_same_function() == 10

    print(nested_simple(), nested_two_args(), nested_same_function())


main()
