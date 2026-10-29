# `nonlocal` finds the nearest enclosing function binding, skipping class bodies.
def f():
    x = 0

    class C:
        x = 1

        def m(self):
            nonlocal x
            x = 2
            return x
    return C
