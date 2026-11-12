from pyhard import loop_invariant, OLD

def f(xs):
    s = 0
    loop_invariant(lambda: s >= 0)
    for x in xs:
        s += x
    return s

print(f([1, 2, 3]))
