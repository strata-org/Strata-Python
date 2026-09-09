# NAIVE MODEL WOULD GET WRONG: applies decorators in eval order (top-to-bottom)
trace = []
def d1(f): trace.append("d1"); return f
def d2(f): trace.append("d2"); return f
@d1
@d2
def f(): pass
# Naive (apply in eval order): d1 first, then d2 → trace ["d1", "d2"]
# CPython: d2 applied first (bottom-to-top) → trace ["d2", "d1"]
assert trace == ["d2", "d1"]
print("BOUNDARY: naive model applies top-to-bottom; CPython applies bottom-to-top")
