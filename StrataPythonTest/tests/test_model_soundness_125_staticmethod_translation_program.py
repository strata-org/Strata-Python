# `@staticmethod` — no self/cls parameter; translator must not add implicit
# first argument
"""
@staticmethod is a method with no `self` or `cls` parameter. It's just
a function namespaced inside a class. The translator must not pass any
implicit first argument. If it treats all methods uniformly (passing
self/cls), staticmethod calls will have wrong arity.
"""
from dataclasses import dataclass
import math


@dataclass
class MathUtils:
    @staticmethod
    def clamp(value: int, lo: int, hi: int) -> int:
        if value < lo:
            return lo
        if value > hi:
            return hi
        return value

    @staticmethod
    def is_even(n: int) -> bool:
        return n % 2 == 0

    @staticmethod
    def max_of_three(a: int, b: int, c: int) -> int:
        if a >= b and a >= c:
            return a
        if b >= c:
            return b
        return c


@dataclass
class Validator:
    @staticmethod
    def is_positive(n: int) -> bool:
        return n > 0

    @staticmethod
    def is_in_range(n: int, lo: int, hi: int) -> bool:
        return lo <= n and n <= hi


def main() -> None:
    # Call staticmethod on class
    assert MathUtils.clamp(5, 0, 10) == 5
    assert MathUtils.clamp(-5, 0, 10) == 0
    assert MathUtils.clamp(15, 0, 10) == 10

    assert MathUtils.is_even(4) == True
    assert MathUtils.is_even(7) == False

    assert MathUtils.max_of_three(1, 5, 3) == 5

    # Call staticmethod on instance (also valid in Python)
    utils: MathUtils = MathUtils()
    assert utils.clamp(3, 0, 5) == 3

    # Validator
    assert Validator.is_positive(5) == True
    assert Validator.is_positive(-1) == False
    assert Validator.is_in_range(5, 0, 10) == True

    print(MathUtils.clamp(5, 0, 10), MathUtils.is_even(4), Validator.is_positive(5))


main()
