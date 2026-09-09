# Chained comparisons (`a < b < c`) evaluate middle operands once — model may
# evaluate twice or miss short-circuit
"""
Python's chained comparisons (`a < b < c`) evaluate `b` exactly ONCE
and expand to `a < b and b < c` with short-circuit semantics. If `b`
is a function call with side effects, it must execute only once. The
model may either:
1. Evaluate `b` twice (once for each comparison) — wrong side effects
2. Not implement chaining at all — wrong semantics for the expression
"""
from dataclasses import dataclass


@dataclass
class Counter:
    value: int

    def next(self: "Counter") -> int:
        self.value = self.value + 1
        return self.value


def in_range(low: int, x: int, high: int) -> bool:
    # Chained comparison: low < x < high
    # Equivalent to: low < x and x < high (x evaluated once)
    return low < x < high


def clamp_check(x: int) -> bool:
    # Chained: 0 <= x <= 100
    return 0 <= x <= 100


def triple_chain(a: int, b: int, c: int, d: int) -> bool:
    # Three-way chain: a < b < c < d
    # Equivalent to: a < b and b < c and c < d
    return a < b < c < d


def mixed_ops(x: int, y: int, z: int) -> bool:
    # Mixed comparison operators: x < y >= z
    # Equivalent to: x < y and y >= z
    return x < y >= z


def side_effect_chain(c: Counter) -> bool:
    # c.next() must be called exactly ONCE
    # CPython: evaluates c.next(), stores result, uses for both comparisons
    # Expands to: tmp = c.next(); 0 < tmp and tmp < 10
    return 0 < c.next() < 10


def main() -> None:
    # Basic chained comparison
    assert in_range(0, 5, 10) == True
    assert in_range(0, 15, 10) == False
    assert in_range(0, -1, 10) == False

    # Boundary: 0 <= x <= 100
    assert clamp_check(0) == True
    assert clamp_check(100) == True
    assert clamp_check(101) == False
    assert clamp_check(-1) == False

    # Triple chain
    assert triple_chain(1, 2, 3, 4) == True
    assert triple_chain(1, 2, 3, 3) == False  # 3 < 3 is False

    # Mixed operators
    assert mixed_ops(1, 5, 3) == True   # 1 < 5 and 5 >= 3
    assert mixed_ops(1, 5, 6) == False  # 1 < 5 and 5 >= 6 → False

    # Side effect: c.next() called exactly once
    c: Counter = Counter(value=0)
    r: bool = side_effect_chain(c)
    # CPython: c.next() returns 1 (called once), 0 < 1 < 10 → True
    # c.value is now 1
    assert r == True
    assert c.value == 1  # Model (double eval): c.value == 2

    # Second call
    r2: bool = side_effect_chain(c)
    # CPython: c.next() returns 2, 0 < 2 < 10 → True, c.value = 2
    assert r2 == True
    assert c.value == 2  # Model (double eval): c.value == 4

    print(r, c.value, r2)


main()
