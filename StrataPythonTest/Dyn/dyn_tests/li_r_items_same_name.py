from pyhard import loop_invariant, OLD

def f(xs, d):
    i = 0
    loop_invariant(lambda: all(k > 0 for k, k in d.items()))
    while i < len(xs):
        i += 1
    return i
