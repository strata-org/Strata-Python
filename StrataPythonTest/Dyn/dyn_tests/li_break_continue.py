from pyhard import loop_invariant, OLD

def f(xs):
    s = 0
    i = 0
    loop_invariant(lambda: 0 <= i <= len(xs))
    while i < len(xs):
        i += 1
        if xs[i - 1] < 0:
            continue
        if xs[i - 1] > 100:
            break
        s += xs[i - 1]
    return s

print(f([1, -2, 3, 200, 4]))
