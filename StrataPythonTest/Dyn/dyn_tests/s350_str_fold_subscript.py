# A % whose left operand folds to a str through a subscript, ("%s %s",)[0], is a format that
# CPython's AST optimizer rewrites into an f-string; the translator rejects it.
class A:
    def __str__(self):
        print("str A")
        return "a"
def f():
    print("f")
    return A()
def g():
    print("g")
    return A()
print(("%s %s",)[0] % (f(), g()))
