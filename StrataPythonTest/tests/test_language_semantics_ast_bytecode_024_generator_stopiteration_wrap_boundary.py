# NAIVE MODEL WOULD GET WRONG: lets StopIteration propagate from generator body
def gen():
    raise StopIteration("from body")
    yield
g = gen()
try:
    next(g)
except RuntimeError as e:
    result = "RuntimeError"
except StopIteration:
    result = "StopIteration"
# Naive (no wrapping): StopIteration propagates. CPython: RuntimeError (PEP 479)
assert result == "RuntimeError"
print("BOUNDARY: naive model propagates StopIteration; CPython wraps as RuntimeError")
