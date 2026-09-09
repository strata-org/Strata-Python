# NAIVE MODEL WOULD GET WRONG: calls __enter__ before checking __exit__
trace = []
class Broken:
    def __enter__(self):
        trace.append("enter")
        return self
    # no __exit__
try:
    with Broken(): pass
except (TypeError, AttributeError): pass
# Naive (call __enter__ first): trace = ["enter"]. CPython: trace = []
assert trace == []
print("BOUNDARY: naive model calls __enter__ first; CPython checks __exit__ first")
