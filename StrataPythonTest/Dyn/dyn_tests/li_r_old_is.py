from pyhard import loop_invariant, OLD

def f(p=1.5):
    i = 0
    loop_invariant(lambda: OLD(p) is p)
    while i < 2:
        i += 1
    return i
