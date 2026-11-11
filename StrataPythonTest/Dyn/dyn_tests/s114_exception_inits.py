# Test: the inits of the exception classes with fields, ImportError's msg, add_note, ExceptionGroup's checks and the repr of a raised class
class MyNE(NameError):
    pass
try:
    MyNE("a", x=1)
except TypeError as t:
    print(t.args[0])
class MyIE(ModuleNotFoundError):
    pass
try:
    MyIE("a", x=1)
except TypeError as t:
    print(t.args[0])
try:
    AttributeError("a", x=1)
except TypeError as t:
    print(t.args[0])
e = NameError("a")
try:
    e.__init__("b", x=1)
except TypeError:
    pass
print(e.args[0])
e = SystemExit(5)
e.__init__()
print(e.code)
e = ImportError(5)
e.args = ("a",)
print(e.__str__())
e = ImportError("a", name="n")
e.__init__()
print(e.msg, e.name)
try:
    from builtins import nope
except ImportError as e:
    print(e.name, e.name_from, e.path, e.msg)
class MyEG(ExceptionGroup):
    pass
try:
    MyEG("m", [KeyboardInterrupt()])
except TypeError as t:
    print(t.args[0])
g = BaseExceptionGroup("m", (KeyboardInterrupt(),))
print(type(g).__name__, g.__str__())
g2 = ExceptionGroup("m", [ValueError(1), KeyError(2)])
print(g2.__str__(), g2.args[0], type(g2.args[1]).__name__)
try:
    g2.message = "x"
except AttributeError as a:
    print(a.args[0])
class E(Exception):
    def __setattr__(self, n, v):
        print("setattr", n)
        object.__setattr__(self, n, v)
e = E()
e.add_note("x")
print(e.__notes__[0])
e = ValueError()
try:
    e.add_note(1)
except TypeError as t:
    print(t.args[0])
e.__notes__ = 5
try:
    e.add_note("a")
except TypeError as t:
    print(t.args[0])
try:
    BaseException().add_note()
except TypeError as t:
    print(t.args[0])
def t():
    class B(Exception):
        __module__ = "builtins"
        def __new__(cls):
            return 5
    raise B
try:
    t()
except TypeError as e:
    print(e.args[0])
