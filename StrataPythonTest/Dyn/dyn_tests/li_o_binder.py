from pyhard import loop_invariant, OLD

def f(d):
    i = 0
    loop_invariant(lambda: all(OLD(d[k]) <= d[k] for k in d))
    loop_invariant(lambda: OLD(all(v > 0 for k, v in d.items())) or True)
    while i < 2:
        i += 1
    return i

print(f({"a": 1}))
