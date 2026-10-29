# Parameters of every kind; defaults are evaluated by the enclosing scope.
d = 1


def f(a, b=d, /, c=2, *args, e, g=d, **kwargs):
    return a, b, c, args, e, g, kwargs


def h(*, k):
    return k
