from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: all((x > 0 for x in xs), k=1))
    while i < len(xs):
        i += 1
    return i
