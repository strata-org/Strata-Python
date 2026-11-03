# Test: __new__ through a user base, the not-safe message by the static base, and the keyword count of the exception inits
class A:
    def __new__(cls, *a):
        return super().__new__(cls, *a)
class C(A, FileNotFoundError):
    pass
try:
    BaseException.__new__(C)
except TypeError as t:
    print(t.args[0])
class C(KeyError, StopIteration):
    pass
c = C(1)
print(c.value, c.args[0])
class B(OSError):
    def __new__(cls, *a):
        return super().__new__(cls, *a)
class X(ValueError, B):
    pass
try:
    X(2, "y")
    print("made")
except TypeError as t:
    print(t.args[0])
def t(f):
    try:
        f()
    except TypeError as e:
        print(e.args[0])
t(lambda: NameError("a", name="n", x=1))
t(lambda: AttributeError(name=1, obj=2, x=3))
t(lambda: ImportError(name=1, path=2, name_from=3, x=4))
t(lambda: NameError(x=1))
