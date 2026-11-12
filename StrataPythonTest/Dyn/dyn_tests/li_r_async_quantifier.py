from pyhard import loop_invariant

def f(xs):
    i = 0
    loop_invariant(lambda: all(x async for x in xs))
    while i < 1:
        i += 1
    return i
