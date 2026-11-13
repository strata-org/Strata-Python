from pyhard import loop_invariant, OLD

def f(d):
    i = 0
    loop_invariant(lambda: all(v > 0 for k, v in OLD(d).items()) is True)
    while i < 2:
        i += 1
    return i
