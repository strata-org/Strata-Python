# Exception tag poisons operators — `PAdd(exception(...), from_int(1))`
# returns Hole; exception silently consumed
"""
When a function returns an exception value (exception(Error)), what
happens if that value flows into a binary operator? E.g.:
  y = might_raise(x)   # returns exception(ValueError)
  z = y + 1            # PAdd(exception(...), from_int(1)) = ???

If PAdd has no case for the `exception` tag, the result is Hole or
an assertion failure. The exception should propagate (z should also
be an exception), but without explicit propagation logic, the exception
is silently consumed and computation continues with garbage.
"""


def validate(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x * 2


def process(x: int) -> int:
    y: int = validate(x)
    # If validate raises, y holds exception(ValueError)
    # CPython: this line is NEVER reached (exception unwinds)
    # Model: PAdd(exception(...), from_int(1)) = ???
    z: int = y + 1
    return z


def chain_operations(x: int) -> int:
    a: int = validate(x)
    b: int = a * 3       # PMul(exception, from_int(3)) = ???
    c: int = b - 10      # PSub(???, from_int(10)) = ???
    return c


def use_in_condition(x: int) -> str:
    y: int = validate(x)
    # If y is exception, what does PLt(exception, from_int(0)) return?
    if y < 0:
        return "negative"
    return "non-negative"


def main() -> None:
    # Normal case: no exception
    assert process(5) == 11   # validate(5)=10, 10+1=11
    assert chain_operations(3) == 8  # validate(3)=6, 6*3=18, 18-10=8

    # Exception case: validate raises
    try:
        result: int = process(-1)
        # CPython: never reaches here
        assert False  # should not execute
    except ValueError:
        pass  # expected

    try:
        result2: int = chain_operations(-5)
        assert False
    except ValueError:
        pass

    assert use_in_condition(5) == "non-negative"

    print(process(5), chain_operations(3))


main()
