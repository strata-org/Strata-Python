from pyhard import loop_invariant, OLD

class P:
    def __init__(self):
        self.xs = [1, 2, 3]

def f(p):
    i = 0
    loop_invariant(lambda: p.xs[0] == 1 and len(p.xs[0:i]) == i and p.xs[::-1][0] == 3)
    while i < len(p.xs):
        i += 1
    return i

print(f(P()))
