# Exception values not checked after function calls — exception flows into
# subsequent operations as garbage instead of propagating
"""
Exceptions are values (exception(...) constructor) in the model. When a
called function raises, it returns exception(...). But the CALLER must
check for this value after every call and skip subsequent statements.
If the translator doesn't insert these checks, the exception value flows
into subsequent operations (y + 1 where y is exception(...)), producing
wrong results instead of propagating the exception.
"""


def validate(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x


def process(x: int) -> int:
    y: int = validate(x)  # returns exception(...) if x < 0
    # CPython: if validate raised, this line is UNREACHABLE
    # Model without check: y is exception(...), then y + 1 is computed
    z: int = y + 1
    return z * 2


def chain(x: int) -> int:
    a: int = validate(x)
    b: int = validate(a)
    c: int = a + b
    return c


def main() -> None:
    # Normal case
    r1: int = process(5)
    assert r1 == 12  # (5 + 1) * 2

    # Exception case: should propagate, not compute garbage
    try:
        r2: int = process(-1)
        # CPython: never reaches here
        assert False
    except ValueError:
        pass  # correct: exception propagated

    # Chain: first call raises, second never executes
    try:
        r3: int = chain(-1)
        assert False
    except ValueError:
        pass  # correct

    print("all passed")


main()
