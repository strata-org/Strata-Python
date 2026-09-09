# If/else branch merge — variable assigned in both branches must be function-
# scoped (not block-scoped); Python has no block scope
"""
After if/else where BOTH branches assign to the same variable, the
merged state must reflect EITHER value depending on which branch was
taken. The solver must handle this as a conditional value.

CPython: deterministic — one branch executes, variable has that value.
Model: if the translator doesn't merge correctly, the variable might
       have the value from the WRONG branch, or be undefined.

CPython result: classify(5) == "positive" (True)
Model result: depends on merge handling — may be wrong or unprovable.
"""


def classify(x: int) -> str:
    if x > 0:
        label: str = "positive"
    elif x < 0:
        label = "negative"
    else:
        label = "zero"
    return label  # must be the value from the taken branch


def abs_manual(x: int) -> int:
    if x >= 0:
        result: int = x
    else:
        result = -x
    return result  # x or -x depending on branch


def max_of_two(a: int, b: int) -> int:
    if a >= b:
        m: int = a
    else:
        m = b
    return m


def conditional_with_computation(x: int) -> int:
    if x > 10:
        y: int = x * 2
    else:
        y = x + 100
    # y is either x*2 or x+100
    return y


def nested_conditional(a: int, b: int) -> int:
    if a > 0:
        if b > 0:
            r: int = a + b
        else:
            r = a
    else:
        r = 0
    return r


def main() -> None:
    assert classify(5) == "positive"
    assert classify(-3) == "negative"
    assert classify(0) == "zero"

    assert abs_manual(7) == 7
    assert abs_manual(-7) == 7
    assert abs_manual(0) == 0

    assert max_of_two(5, 3) == 5
    assert max_of_two(3, 5) == 5
    assert max_of_two(4, 4) == 4

    assert conditional_with_computation(20) == 40
    assert conditional_with_computation(5) == 105

    assert nested_conditional(3, 4) == 7
    assert nested_conditional(3, -1) == 3
    assert nested_conditional(-1, 5) == 0

    print(classify(5), abs_manual(-7), max_of_two(5, 3))


main()
