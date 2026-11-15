# Test: the module's own frame counts toward the Python call depth: 899 nested calls run
def f(n):
    if n == 0:
        return 0
    return f(n - 1)
print(f(898))
