from pyhard import loop_invariant, OLD

def f(n):
    fs = []
    i = 0
    loop_invariant(lambda: len(fs) == i)
    while i < n:
        fs.append(lambda: i)
        i += 1
    return [g() for g in fs]

print(f(3))
