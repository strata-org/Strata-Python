# `assert`: the test is a condition, so `a and b` tests each operand once.  Only the failing
# side evaluates the message, then raises the built-in `AssertionError` class called on it,
# even if the name `AssertionError` is bound.
AssertionError = KeyError
assert c
assert c, m
assert a and b, f"{a}"
assert not c, g()
assert a or b

for x in xs:
    assert x, x

def f(x):
    assert x
    return x
