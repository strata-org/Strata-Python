from pyhard import loop_invariant, OLD

def f(d):
    n = 0
    loop_invariant(lambda: n <= len(d))
    for k in d:
        n += 1
    return n

print(f({"a": 1, "b": 2}))
