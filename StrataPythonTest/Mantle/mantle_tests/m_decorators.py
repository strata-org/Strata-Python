# Decorators and non-constant defaults: decorators are evaluated top to bottom, then the
# defaults, and the decorators are applied bottom to top.  A closure takes its free cells,
# then its default cells.  In `order`, the decorator is a parameter, and the calls run as
# CPython runs them: log(1), log(2), log("a"), log("c"), then the decorators.
def trace(fn):
    return fn


def tag(name):
    return trace


@trace
@tag("t")
def f(a, b=[], *, c=len("x"), d=0):
    return a, b, c, d


def outer(n):
    def g(x=n + 1):
        return x + n
    return g


def order(log):
    @log(1)
    @log(2)
    def h(a=log("a"), b=1, *, c=log("c")):
        pass
    return h
