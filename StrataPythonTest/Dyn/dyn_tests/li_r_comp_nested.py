from pyhard import loop_invariant

y = 1

def f(xs):
    a = [y for y in xs]
    i = 0
    loop_invariant(lambda: i >= 0)
    loop_invariant(lambda: all(all(y > 0 for w in v) for v in xs))
    while i < 1:
        i += 1
    loop_invariant(lambda: i >= 0)
    while i < 2:
        i += 1
    return a
