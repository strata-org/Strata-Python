from pyhard import loop_invariant, OLD

def f():
    seen = []
    k = -1
    loop_invariant(lambda: k < 3)
    for k in range(3):
        seen.append(k)
    return seen

print(f())
