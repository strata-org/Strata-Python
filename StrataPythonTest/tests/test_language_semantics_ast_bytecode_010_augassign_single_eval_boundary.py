# NAIVE MODEL WOULD GET WRONG: desugars a[f()] += 1 as a[f()] = a[f()] + 1
calls = []
def f():
    calls.append(1)
    return 0
a = [10]
a[f()] += 5
# Naive desugaring: f() called twice (once for load, once for store)
# CPython: f() called once
assert len(calls) == 1
assert a == [15]
print("BOUNDARY: naive desugaring calls f() twice; CPython calls it once")
