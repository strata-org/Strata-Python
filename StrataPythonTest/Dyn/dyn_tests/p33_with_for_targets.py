# `with … as`, tuple and starred `for` targets, augmented and annotated assignment bind.
def f(path, pairs):
    with open(path) as fh, open(path) as (g):
        data = fh.read()
    for a, (b, *c) in pairs:
        pass
    n = 0
    n += 1
    m: int = 2
    declared: int
    obj.attr = 1
    obj[0] = 2
    return data, a, b, c, n, m
