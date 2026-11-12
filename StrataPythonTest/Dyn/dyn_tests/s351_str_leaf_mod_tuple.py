# A % whose left operand has a str constant among its leaves but folds to an int, a tuple or bytes is
# no format: CPython's AST optimizer leaves it alone. The int and tuple ones raise TypeError at run
# time; the bytes one formats its items after evaluating both, as here.
x = 5
for f in [lambda: ("a", 1)[1] % (x,), lambda: ("a", "b") % (x,), lambda: ("%s",) * 2 % (x,)]:
    try:
        f()
    except TypeError as e:
        print("TypeError", e)
class A:
    def __bytes__(self):
        print("bytes A")
        return b"a"
def f():
    print("f")
    return A()
def g():
    print("g")
    return A()
print((b"%s %s",)[0] % (f(), g()))
