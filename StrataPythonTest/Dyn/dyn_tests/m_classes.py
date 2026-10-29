# Classes: a docstring, the class body's own names, then globals and builtins, `del`, `+=` and
# `import` in a class body, `global` and `nonlocal` (with `del`) in a class body, starred
# bases and `**` keywords, a class decorator, private parameters, whose keywords are mangled
# too, and a class body reading the `__annotations__` it sets up.
g = 1


def deco(cls):
    return cls


@deco
class A:
    "Doc."
    a = g
    b = a + len("x")
    b += 1
    import os
    del a

    def m(self):
        return self.b


def outer(bases, kws):
    n = 0

    class B(A, *bases, metaclass=type, **kws):
        global g
        nonlocal n
        g = 2
        n = n + 1
        del n
    return B


class Priv:
    def m(self, __x, __d=g, *, __k=1):
        return __x, __d, __k

    def outer(self):
        def inner(__z):
            return __z
        return inner(_Priv__z=1)

    f = lambda self, *, __y=2: __y


class Config:
    host: str = "localhost"
    fields = list(__annotations__)
