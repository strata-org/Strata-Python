from pyhard import loop_invariant, OLD

def f(xs, d):
    i = 0
    loop_invariant(lambda: all(x > 0 for x in xs) and any(x > 1 for x in xs if x != 0))
    loop_invariant(lambda: all(v > 0 for k, v in d.items()) and any(k == "a" for k, v in d.items()))
    loop_invariant(lambda: all(len(k) == 1 for k in d.keys()) and all(v > 0 for v in d.values()))
    while i < len(xs):
        i += 1
    return i

print(f([1, 2], {"a": 1}))
