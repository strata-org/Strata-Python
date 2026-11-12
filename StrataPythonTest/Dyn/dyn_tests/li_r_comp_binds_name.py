from pyhard import loop_invariant, OLD

x = 7

def f(xs):
    ys = [x for x in xs]
    i = 0
    loop_invariant(lambda: x == 7)
    while i < len(ys):
        i += 1
    return i
