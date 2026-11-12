from pyhard import loop_invariant, OLD

def f(xs):
    loop_invariant(lambda: len(xs) >= 0)
    for x in xs:
        if x < 0:
            raise ValueError(x)
    return 0

try:
    f([1, -1])
except ValueError as e:
    print("ValueError", e)
