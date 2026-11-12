from pyhard import loop_invariant, OLD

xs = []

def f(xs):
    i = 0
    loop_invariant(lambda: all(x > 0 for x in xs))
    while i < len(xs):
        i += 1
    return i

print(f([1, 2]))
