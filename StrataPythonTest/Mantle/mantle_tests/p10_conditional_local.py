# A local assigned in one branch only is still local.
def f(c):
    if c:
        v = 1
    return v


def g(xs):
    for i in xs:
        last = i
    return last
