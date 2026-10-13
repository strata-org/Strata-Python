# Closures: a captured parameter, `del` of a free variable, a cell passed through a function
# that does not use it, two nested functions with the same name, two cells captured in an
# order that is not alphabetical, and a cell read before it is assigned.
def make(p):
    def get():
        return p

    def drop():
        nonlocal p
        del p
    return get, drop


def outer():
    x = 1

    def mid():
        def inner():
            return x
        return inner
    return mid


def twice(flag):
    if flag:
        def h():
            return flag
    else:
        def h():
            return not flag
    return h


def pair(a, b):
    def g():
        return b, a
    return g


def early():
    def h():
        return y
    r = y
    y = 1
    return h, r
