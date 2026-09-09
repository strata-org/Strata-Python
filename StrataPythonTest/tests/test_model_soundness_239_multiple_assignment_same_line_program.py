# Sequential assignment semantics — reassignment doesn't affect prior uses;
# swap-via-temp is the critical test; likely correct (verification)
"""
The subset says "No x = y = z = 1 chains" and "No tuple unpacking
a, b = 1, 2" — both are OUT.

But what about SEQUENTIAL assignments on separate lines that interact?

    a = compute()
    b = a + 1
    a = b + 1  # a is now rebound; old a is gone

The model must handle that `b = a + 1` uses the CURRENT value of a
(from the first assignment), and `a = b + 1` rebinds a (the second
assignment doesn't affect b's value).

This is basic SSA / sequential assignment semantics. The model should
handle it correctly, but it's worth verifying.

Uses ONLY confirmed-accepted constructs: int, assignment, arithmetic.
"""


def sequential_assignments() -> int:
    a: int = 1
    b: int = a + 1  # b = 2
    c: int = b + 1  # c = 3
    return a + b + c  # 1 + 2 + 3 = 6


def reassignment_doesnt_affect_prior() -> int:
    x: int = 10
    y: int = x  # y = 10
    x = 20      # x rebound; y still 10
    return x + y  # 20 + 10 = 30


def swap_via_temp() -> bool:
    a: int = 1
    b: int = 2
    temp: int = a
    a = b
    b = temp
    return a == 2 and b == 1


def accumulate_with_reassignment() -> int:
    total: int = 0
    x: int = 1
    total = total + x  # total = 1
    x = x * 2          # x = 2
    total = total + x  # total = 3
    x = x * 2          # x = 4
    total = total + x  # total = 7
    return total


def fibonacci_step() -> int:
    a: int = 0
    b: int = 1
    # One Fibonacci step: new_a = b, new_b = a + b
    temp: int = b
    b = a + b  # b = 1
    a = temp   # a = 1
    # Another step
    temp = b
    b = a + b  # b = 2
    a = temp   # a = 1
    return b  # 2


def main() -> None:
    assert sequential_assignments() == 6
    assert reassignment_doesnt_affect_prior() == 30
    assert swap_via_temp() == True
    assert accumulate_with_reassignment() == 7
    assert fibonacci_step() == 2

    print(sequential_assignments(), reassignment_doesnt_affect_prior(),
          fibonacci_step())


main()
