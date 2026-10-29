# A walrus in an inlined comprehension binds in the enclosing function, even when nested;
# its target is an ordinary local there, not a cell.  At module level it is a global.
def f(xs):
    a = [(last := x) for x in xs]
    return a, last


def g(rows):
    a = [[(cell := c) for c in row if c] for row in rows]
    return a, cell


def h(xs):
    total = 0

    def add():
        nonlocal total
        return [(total := total + x) for x in xs]

    return add


evens = [(seen := n) for n in range(4) if n % 2 == 0]
