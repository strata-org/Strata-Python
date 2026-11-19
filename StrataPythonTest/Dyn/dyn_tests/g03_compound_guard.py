# P4 (reason-carrying exit): the guard has two false edges, and every guard operation can raise.
def c(it):
    n = 0
    while (x := next(it, None)) is not None and ok(x):
        n += handle(x)
    return n
