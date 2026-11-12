from pyhard import loop_invariant, OLD

def f(t):
    n = 0
    loop_invariant(lambda: n <= len(t))
    for c in t:
        n += 1
    return n

print(f("abc"))
