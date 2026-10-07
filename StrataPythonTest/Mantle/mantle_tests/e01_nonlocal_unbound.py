def f():
    def g():
        nonlocal x
        x = 1
    return g
