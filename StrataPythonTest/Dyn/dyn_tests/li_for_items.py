from pyhard import loop_invariant, OLD

def f(d):
    s = 0
    loop_invariant(lambda: s >= 0)
    for k, v in d.items():
        s += v
    return s

print(f({"a": 1, "b": 2}))
