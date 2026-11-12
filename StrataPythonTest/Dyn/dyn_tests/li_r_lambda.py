from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: (lambda: i) is not None)
    while i < len(xs):
        i += 1
    return i
