# Annotations, as CPython 3.12 evaluates them: a module or class body with an annotated
# assignment sets up __annotations__ first.  A simple name's annotation is stored there,
# after its value; a non-simple target's is evaluated and dropped; a private name is mangled.
# In a function the annotation is not evaluated, but its names still count, so `h` captures
# `o`, and a `yield` in it makes a generator.  A class body's annotation can read the enclosing
# function's variable.  An annotation inside a loop also sets up __annotations__ (after
# __qualname__, before __doc__); one only in a method does not.  __annotations__ is the
# namespace's, however the enclosing scope binds the name.
# A module that sets up __annotations__ can read it, and so can its functions.
from dataclasses import dataclass

n: int = 1
(m): int = 2


@dataclass
class P:
    x: int
    y: int = 0
    __z: str = ""
    if n:
        w: float = 0.0


class R:
    """Doc."""
    for i in range(2):
        a: int = i


class S:
    def m(self):
        b: int = 0
        return b


def f(o):
    k: int = 3
    o.a: int = 4

    class Q:
        v: o

    def h():
        j: o = 0
        return j
    return k, Q, h


def g():
    __annotations__ = 5

    class C:
        x: int
        y = __annotations__
    return C


def gen():
    x: (yield) = 1


ann = __annotations__


def anns():
    return __annotations__
