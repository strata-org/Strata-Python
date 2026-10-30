# A constant default. CPython 3.12 evaluates a default once, at the def, so every call gets the
# same object and f() is f() is True. The translation rebuilds the constant in the prologue at
# each call (docs/PythonToDyn.md, §5.4); this program pins that translation.
def f(a=1000):
    return a

print(f() is f())
