# A global that shadows a builtin, assigned only conditionally.
import sys

if sys.argv:
    len = lambda xs: 0


def f(xs):
    return len(xs)
