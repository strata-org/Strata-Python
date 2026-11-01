# Test: unbounded recursion stops at the model's call depth, before CPython's RecursionError
def f(n):
    return f(n + 1)
f(0)
