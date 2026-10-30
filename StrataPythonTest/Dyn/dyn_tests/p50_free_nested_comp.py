# A name free in three nested comprehensions is the function's local, read from its cell.
def f(k, a):
    return [[[k for _ in c] for c in b] for b in a]
