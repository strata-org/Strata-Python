from pyhard import loop_invariant, OLD

class Count:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return iter(range(self.n))

def f(c):
    s = 0
    loop_invariant(lambda: s >= 0)
    for x in c:
        s += x
    return s

print(f(Count(3)))
