# The dict a callee receives for **kwargs is safe to mutate: a call site always
# builds it fresh, so the caller's own dict is unaffected.
def f(**kwargs):
    kwargs["added"] = 1
    print(len(kwargs))

m = {"a": 1}
f(**m)
print(m)
f(**m)
print(m)

# The *args tuple is likewise fresh per call.
def g(*args):
    print(args)
xs = [1, 2]
g(*xs)
xs.append(3)
g(*xs)
