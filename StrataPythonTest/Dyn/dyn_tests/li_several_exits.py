from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: 0 <= i <= len(xs))
    while i < len(xs):
        if xs[i] == 0:
            return "zero"
        if xs[i] < 0:
            break
        i += 1
    else:
        return "all positive"
    return "negative"

print(f([1, 2]), f([1, 0]), f([1, -1]))
