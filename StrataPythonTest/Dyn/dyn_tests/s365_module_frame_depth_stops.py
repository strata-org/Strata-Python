# Test: the module's own frame counts toward the Python call depth: the 900th nested call stops
# with a gap, where CPython, which allows 1,000 frames, answers
def f(n):
    if n == 0:
        return 0
    return f(n - 1)
print(f(899))
