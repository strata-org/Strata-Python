from pyhard import loop_invariant, OLD

def f(xs):
    n = 0
    loop_invariant(lambda: n >= 0)
    for x in xs:
        n += x
    return n

print(f([1, 2]))
