from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: i >= 0)
    while xs[i] > 0:
        i += 1
    return i

try:
    f([1, 2])
except IndexError:
    print("IndexError")
