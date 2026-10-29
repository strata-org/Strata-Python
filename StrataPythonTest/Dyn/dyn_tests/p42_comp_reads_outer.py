# A comprehension reading a local of the enclosing function does not make it a cell; a
# generator expression or a lambda reading it does.
def f(xs, n):
    k = 2
    return [x * k + n for x in xs]


def g(xs):
    k = 2
    return (x * k for x in xs)


def h(xs):
    k = 2
    return [lambda: k for x in xs]


def outer():
    m = 1

    def inner(xs):
        return [x + m for x in xs]

    return inner
