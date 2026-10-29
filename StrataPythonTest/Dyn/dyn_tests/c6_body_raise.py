# A loop body that raises: the exception must leave the loop, not end it.
def boom():
    raise ValueError("body")

def f(xs):
    for x in xs:
        boom()
    return 0
