from pyhard import loop_invariant, OLD

allocated = 0

def f(xs, d):
    i = 0
    loop_invariant(lambda: len(OLD(xs)) == len(xs) + 1 or True)
    loop_invariant(lambda: allocated == OLD(allocated) + 1 or True)
    loop_invariant(lambda: len(OLD(d)["k"]) == len(d["k"]))
    while i < 2:
        i += 1
    return i

print(f([1], {"k": "v"}))
