from pyhard import loop_invariant, OLD

def f(a, b, n):
    i = 0
    loop_invariant(lambda: (a or b) == (b if not a else a) and (a and b) != 0)
    while i < n:
        i += 1
    return i

print(f(1, 2, 2))
