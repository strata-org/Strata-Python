# Closures: a read, late binding, a `nonlocal` write, and pass-through capture.
def reader():
    x = 1

    def r():
        return x
    x = 2
    return r


def counter():
    n = 0

    def inc():
        nonlocal n
        n += 1
        return n
    return inc


def outer(p):
    def middle():
        def inner():
            return p
        return inner
    return middle
