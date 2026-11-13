from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: OLD(all(x > 0 for x in xs)) or True)
    while i < 2:
        i += 1
    return i

print(f([1]))
