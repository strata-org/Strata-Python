# A lambda inside an inlined comprehension: the iteration variable it captures is a cell
# of the enclosing scope, flagged `comp_cell`, fresh on each run of the comprehension.  A
# local of the same name becomes a cell too.
def f(xs):
    return [lambda: x for x in xs]


def g(xs):
    x = 0
    fs = [lambda: x for x in xs]
    return fs, x


def h(xs, ys):
    return [lambda: (x, y) for x in xs for y in ys]


def k(xs):
    return [lambda y=x: y for x in xs]


fs = [lambda: n for n in range(3)]
