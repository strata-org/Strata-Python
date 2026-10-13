# Lambdas: one that captures a parameter, one with every kind of parameter and a constant
# default, a lambda in a lambda, a generator lambda (a stub), and one with a non-constant
# default, whose `yield` makes the enclosing function a generator (a stub).
def adder(n):
    return lambda x: x + n


g = lambda a, /, b, *r, c=1, **kw: (a, b, r, c, kw)
h = lambda: lambda z: z
gen = lambda: (yield)
bad = lambda d=[]: d


def yields():
    return lambda x=(yield): x
