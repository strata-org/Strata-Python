# A walrus in a comprehension binds in the enclosing function, or at module level.
def f(xs):
    if any((hit := x) > 0 for x in xs):
        return hit
    return [last := x for x in xs], last


ys = [total := y for y in range(3)]


def g(xs):
    return [[(deep := y) for y in x] for x in xs], deep


def h(xs):
    if (n := len(xs)) > 1:
        return n
