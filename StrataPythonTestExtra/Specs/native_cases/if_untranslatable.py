# An assert under an `if` whose condition doesn't translate is recorded as dropped. It stays a
# precondition, as before, for ToLaurel.
def f(x: int, n: int) -> None:
    if x.bit_length() > 3:
        assert x >= 0, "x is not negative"
    if x > "a":
        assert n >= 1, "n is positive"
