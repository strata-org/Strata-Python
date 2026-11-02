# Test: writes to a function's __name__, __annotations__ and its own attributes
def f(x):
    return x
f.__name__ = "g"
f.tag = 5
f.__annotations__ = {"x": 1}
print(f.__name__, f.tag, f.__annotations__["x"], f.__dict__["tag"])
del f.tag
f.__name__ = 3
