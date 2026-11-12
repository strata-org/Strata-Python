from pyhard import loop_invariant, OLD

def f(xs, d):
    i = 0
    loop_invariant(lambda: all(v for v in d.values(1)))
    while i < len(xs):
        i += 1
    return i
