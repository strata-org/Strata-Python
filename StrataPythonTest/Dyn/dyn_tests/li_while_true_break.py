from pyhard import loop_invariant, OLD

def f(xs):
    i = 0
    loop_invariant(lambda: 0 <= i <= len(xs))
    while True:
        if i == len(xs):
            break
        i += 1
    return i

print(f([1, 2, 3]))
