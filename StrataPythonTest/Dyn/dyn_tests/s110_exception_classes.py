# Test: exceptions made by calling their classes, their fields, and raise
class E(Exception):
    pass
e = ValueError("a", 2)
print(e.args[0], e.args[1], (e).__str__(), ValueError("a").__repr__())
print(StopIteration(1, 2).value, SystemExit().code is None, NameError("n", name="v").name)
print(AttributeError("a", name="n", obj=1).obj, ImportError("m", name="x").msg, (KeyError("k")).__str__())
o = OSError(2, "no file")
print(type(o) is FileNotFoundError, o.errno, o.strerror, (o).__str__(), (OSError(2, "no", "f.txt")).__str__())
g = ExceptionGroup("m", [ValueError(1)])
print(type(BaseExceptionGroup("m", [ValueError(1)])) is ExceptionGroup, g.message, (g).__str__(), type(g.exceptions[0]) is ValueError)
e.add_note("n1")
print(e.__notes__[0])
e.x = 5
print(e.x)
try:
    raise E
except E as x:
    print("E", x.args == (), x.__traceback__ is not None)
try:
    raise E("m") from ValueError("v")
except E as x:
    print((x).__str__(), (x.__cause__).__str__(), x.__suppress_context__)
try:
    try:
        raise KeyError(1)
    except KeyError:
        raise E("inner")
except E as x:
    print(type(x.__context__) is KeyError)
class C:
    def __enter__(self):
        print("enter")
        return 7
    def __exit__(self, t, v, tb):
        print("exit", t is ValueError, (v).__str__())
        return True
with C() as v:
    print("body", v)
    raise ValueError("w")
print("after with")
raise E("end")
