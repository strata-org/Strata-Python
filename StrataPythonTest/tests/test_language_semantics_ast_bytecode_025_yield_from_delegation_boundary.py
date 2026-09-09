# NAIVE MODEL WOULD GET WRONG: doesn't forward send() to sub-generator
def sub():
    received = yield "first"
    yield f"got: {received}"
def outer():
    yield from sub()
g = outer()
assert next(g) == "first"
result = g.send("hello")
# Naive (no send forwarding): sub doesn't receive "hello". CPython: forwards it
assert result == "got: hello"
print("BOUNDARY: naive model drops send(); CPython forwards to sub-generator")
