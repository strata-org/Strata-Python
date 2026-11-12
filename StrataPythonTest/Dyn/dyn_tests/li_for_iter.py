from pyhard import loop_invariant, OLD

def f(xs):
    it = iter(xs)
    n = 0
    loop_invariant(lambda: n >= 0)
    for x in it:
        n += 1
    return n

print(f([4, 5]))
