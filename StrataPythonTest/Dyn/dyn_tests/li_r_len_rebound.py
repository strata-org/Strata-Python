from pyhard import loop_invariant, OLD

def len(x):
    return 0

def f(xs):
    i = 0
    loop_invariant(lambda: len(xs) >= 0)
    while i < 2:
        i += 1
    return i
