# Test: object.__ne__ on a built-in value or a function inverts the type's own ==
a = object.__ne__(5, 5)
b = object.__ne__(1, 2)
def f():
    pass
c = f.__ne__(f)
