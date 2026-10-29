# `del x` binds: `x` is local, and reading it afterwards raises.
def f():
    x = 1
    del x
    return x


y = 1
del y
