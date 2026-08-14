# Function-body assertions are modeled as preconditions, so OLD is invalid.
def f(x: int) -> int:
    assert OLD(x) >= 0
    ...
