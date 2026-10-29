# Nested comprehensions are all inlined; a generator expression inside one is not, and is a
# child of the enclosing function.
def f(rows):
    a = [[c * r for c in row] for r, row in rows]
    b = {k: {v for v in vs} for k, vs in rows}
    g = [list(q for q in row if q) for row in rows]
    return a, b, g


def h(rows):
    return [[(i, j) for j in range(i)] for i in (len(r) for r in rows)]
