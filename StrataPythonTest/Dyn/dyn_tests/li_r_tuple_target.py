from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: all(a > b for a, b in xs))
    while i < len(xs):
        i += 1
    return i
