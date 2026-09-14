def outer2():
    x = 1
    def inner2():
        nonlocal x
        x = 2
    return x
