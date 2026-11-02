# Test: __build_class__ of a function renamed "<body>", which is no class body
def f():
    pass
f.__name__ = "<body>"
C = __build_class__(f, "C")
