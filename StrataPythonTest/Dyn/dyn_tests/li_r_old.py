from pyhard import loop_invariant, OLD

def f(xs, d):
    i = 0
    loop_invariant(lambda: OLD(i) == 0)
    while i < len(xs):
        i += 1
    return i
