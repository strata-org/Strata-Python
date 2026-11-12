from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: abs(i) >= 0)
    while i < len(xs):
        i += 1
    return i
