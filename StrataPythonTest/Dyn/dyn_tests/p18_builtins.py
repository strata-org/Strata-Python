# Builtins are global implicit, including ones outside the old translator's list.
def f(xs):
    return sorted(reversed(xs)), divmod(7, 2), frozenset(xs), memoryview(b""), vars()
