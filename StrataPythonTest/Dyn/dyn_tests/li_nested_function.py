from pyhard import loop_invariant, OLD

def outer(n):
    def inner():
        i = 0
        loop_invariant(lambda: 0 <= i <= n)
        while i < n:
            i += 1
        return i
    return inner()

print(outer(3))
