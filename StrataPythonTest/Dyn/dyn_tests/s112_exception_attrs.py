# Test: writes of an exception's attributes and its __dict__, and a __context__ cycle that the new exception is not on
def run(name, f):
    try:
        f()
    except Exception as e:
        print(name, type(e).__name__, e.args[0])
e = ValueError("v")
def ctx():
    e.__context__ = 1
def sup():
    e.__suppress_context__ = 1
def tb():
    e.__traceback__ = 1
def dargs():
    del e.args
def cause():
    e.__cause__ = 1
def dctx():
    del e.__context__
run("context", ctx)
run("suppress", sup)
run("traceback", tb)
run("args", dargs)
run("cause", cause)
run("del context", dctx)
e.__cause__ = KeyError("k")
print(e.__suppress_context__, type(e.__cause__) is KeyError)
e.__suppress_context__ = False
e.args = [1, 2]
print(e.args[0], e.args[1], type(e.args) is tuple)
e.__traceback__ = None
print(e.__traceback__)
n = NameError("m")
n.name = "q"
print(n.name)
a = ValueError("a")
b = KeyError("b")
a.__context__ = b
b.__context__ = a
try:
    try:
        raise a
    except ValueError:
        raise TypeError("c")
except TypeError as c:
    print(c.__context__ is a, a.__context__ is b, b.__context__ is a)
f = ValueError("m")
f.y = 2
d = f.__dict__
d["x"] = 1
print(f.x, f.__dict__ is d, d["y"])
class U(Exception):
    pass
u = U()
u.__dict__["z"] = 3
print(u.z)
