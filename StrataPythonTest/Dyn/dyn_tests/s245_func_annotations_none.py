# Test: setting a function's __annotations__ to None gives it a new empty dict
def f(x: int):
    pass
f.__annotations__ = None
r = f.__annotations__
