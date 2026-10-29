# `import a.b` binds `a`; `a.b.f` resolves through it.
import os.path
import a.b.c


def f():
    return os.path.join("x", "y"), a.b.c.g()
