from pyhard import loop_invariant, OLD

g = 3

def outer(x):
    def inner(n):
        i = 0
        loop_invariant(lambda: OLD(g) == g and OLD(x) == x and i <= n)
        while i < n:
            i += 1
        return i
    return inner(2)

print(outer(1))
