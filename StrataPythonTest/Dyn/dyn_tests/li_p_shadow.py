from pyhard import loop_invariant, OLD

def f(xs):
    x = -100
    i = 0
    loop_invariant(lambda: all(x > 0 for x in xs) and x == -100)
    while i < len(xs):
        i += 1
    return i

print(f([1, 2]))
