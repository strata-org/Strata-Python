from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: all(x > y for x in xs for y in xs))
    while i < len(xs):
        i += 1
    return i
