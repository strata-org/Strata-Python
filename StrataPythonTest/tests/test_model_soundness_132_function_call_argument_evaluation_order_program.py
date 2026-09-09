# Argument evaluation order — left-to-right with state threading; side-
# effecting args in wrong order produce wrong values
"""
Python evaluates function arguments LEFT TO RIGHT before the call.
If arguments have side effects, the order matters. The model must
evaluate arguments in the same order as CPython.

`f(a(), b(), c())` evaluates a(), then b(), then c(), then calls f.
If the model evaluates in a different order (or all at once), side
effects occur in the wrong sequence.
"""
from dataclasses import dataclass


@dataclass
class Sequence:
    next_val: int

    def next(self: "Sequence") -> int:
        result: int = self.next_val
        self.next_val = self.next_val + 1
        return result


def three_args(a: int, b: int, c: int) -> list[int]:
    return [a, b, c]


def two_args(x: int, y: int) -> int:
    return x - y  # order matters: x - y != y - x


def main() -> None:
    # Arguments evaluated left to right
    seq: Sequence = Sequence(next_val=0)
    result: list[int] = three_args(seq.next(), seq.next(), seq.next())
    # CPython: evaluates seq.next() three times, left to right
    # First call: returns 0, next_val becomes 1
    # Second call: returns 1, next_val becomes 2
    # Third call: returns 2, next_val becomes 3
    assert result == [0, 1, 2]

    # Order matters for non-commutative operations
    seq2: Sequence = Sequence(next_val=10)
    diff: int = two_args(seq2.next(), seq2.next())
    # First arg: seq2.next() = 10 (next_val becomes 11)
    # Second arg: seq2.next() = 11 (next_val becomes 12)
    # Result: 10 - 11 = -1
    assert diff == -1

    # If evaluated right-to-left: 11 - 10 = 1 (WRONG)

    print(result, diff)


main()
