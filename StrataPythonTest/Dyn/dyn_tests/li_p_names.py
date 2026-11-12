from pyhard import loop_invariant, OLD

g = 10

def outer(k):
    def f(n):
        i = 0
        loop_invariant(lambda: i <= n <= g and k == k and i is not None)
        while i < n:
            i += 1
        return i
    return f(3)

print(outer(1))
