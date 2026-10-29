# A local with a global's or a builtin's name, assigned under `if` or in a loop, is local.
total = 0


def f(xs):
    if xs:
        total = 1
        len = 2
    while xs:
        total += 1
        xs = xs[1:]
    return total, len


def g(xs):
    for total in xs:
        pass
    return total
