# NAIVE MODEL WOULD GET WRONG: evaluates *args before positional args
trace = []
def f(*a, **k): return a
def A(): trace.append("A"); return 1
def B(): trace.append("B"); return [2, 3]
def C(): trace.append("C"); return 4
result = f(A(), *B(), C())
# Naive (separate positional from splats): might eval B before C, or A,C then B
# CPython: strict textual order A, B, C
assert trace == ["A", "B", "C"]
print("BOUNDARY: naive model might reorder splats; CPython guarantees textual order")
