# More declared shapes, as written.  A class-level default of a field; a ClassVar too;
# Annotated metadata; each annotation of a name in order, a conditional one marked; private
# names mangled in annotations and bases; a computed base, a metaclass, keywords passed with
# **, a decorator; every binding of __slots__, as written; the functional TypedDict and
# NamedTuple forms state nothing.  A parenthesized target is no field; a three-arm union; an
# __init__ without a first parameter.  The self.x: T of an __init__ are fields only while
# self keeps its binding: a self bound again in the body, by an import, or by a nonlocal
# self, in a function or a class body, through any depth (but not one that refers to an
# inner function's own self) drops them, and so does a bare annotation of self (on the safe
# side); a nested class body's own self does not, nor a comprehension's own variable, but an
# assignment expression in a comprehension does.  A generator __init__ is a stub and
# declares nothing, and so does a decorated __init__ and an __init__ outside a class.  Each
# overload of __init__ counts; a field after an early return is not marked conditional, which
# is syntactic.  A global __slots__ or __init__ is bound outside the class and states nothing.
from typing import Annotated, ClassVar, NamedTuple, TypedDict, overload

flag = True


class Account:
    currency: str = "EUR"
    rate: ClassVar[float] = -1.5
    pair: tuple = (1, 2)
    n: Annotated[int, "meta", ...]
    x: int = 1
    x: str
    if flag:
        x: bytes

    def __init__(self):
        self.p: int
        self.q: int = 1


class Outer:
    class __Base:
        pass
    __T = int

    z: __T

    class Inner(__Base):
        pass


def make_base():
    return object


class Meta(type):
    pass


opts = {"metaclass": Meta}


def deco(c):
    return c


@deco
class Odd(make_base(), metaclass=Meta):
    pass


a = "p"
b = "q"


class Spread(**opts):
    __slots__: tuple = ("a",)


class S1:
    __slots__ = [a, b]


class S2:
    __slots__ = ["a", "b"]


class S3:
    if flag:
        __slots__ = ("a",)
    else:
        __slots__ = "b"
    __slots__ += ("c",)
    __slots__ = s = ("d",)
    __slots__, t = ("e",), 1


M = TypedDict("M", {"x": int})
P = NamedTuple("P", [("x", int)])


class R1:
    def __init__(self, other):
        self = other
        self.x: int = 1


class R2:
    def __init__(self):
        import os as self
        self.x: int = 1


class R3:
    def __init__(self, other):
        def f():
            nonlocal self
            self = other
        f()
        self.x: int = 1


class R4:
    def __init__(__s, other):
        __s = other
        __s.x: int = 1


class Gen:
    def __init__(self):
        self.x: int = 1
        yield


def __init__(self):
    self.top: int = 1


def g():
    def __init__(self):
        self.inner: int = 1
    return __init__


class Forms:
    (x): int = 1
    u: int | str | None
    v: make_base().__class__ = b"x"


class Star:
    def __init__(*args):
        pass


class S4:
    __slots__, t = ("a",), 1
    [__slots__, t] = ("b",), 1
    *__slots__, t = "c", "d", 1


class R5:
    def __init__(self):
        class Helper:
            self = R1
            self.h = 1
        self.b: int = 1


class R6:
    def __init__(self):
        def f():
            self = 1

            def g():
                nonlocal self
                self = 2
            g()
        f()
        self.b: int = 1


class R7:
    def __init__(self):
        self: "R7"
        self.c: int = 1


class Over:
    @overload
    def __init__(self, x: int) -> None: ...

    @overload
    def __init__(self, x: str) -> None: ...

    def __init__(self, x):
        self.x: int = x


class Two:
    def __init__(self, other):
        def f():
            def g():
                nonlocal self
                self = other
            g()
        f()
        self.x: int = 1


class Chain:
    def __init__(self, other):
        def f():
            nonlocal self

            def g():
                nonlocal self
                self = other
            g()
        f()
        self.x: int = 1


class ViaClass:
    def __init__(self, other):
        class K:
            def m(_):
                nonlocal self
                self = other
        K().m()
        self.x: int = 1


class ViaClassBody:
    def __init__(self, other):
        def f():
            class K:
                nonlocal self
                self = other
        f()
        self.x: int = 1


class InFunc:
    def __init__(self):
        def f():
            class H:
                self = 1
        f()
        self.x: int = 1


class Deep:
    def __init__(self):
        class A:
            class B:
                self = 1
        self.x: int = 1


class DeepInFunc:
    def __init__(self):
        def f():
            class A:
                class B:
                    self = 1
        f()
        self.x: int = 1


class Early:
    def __init__(self, ok):
        if not ok:
            return
        self.x: int = 1


class CM:
    @classmethod
    def __init__(cls):
        cls.a: int = 1


class CompVar:
    def __init__(self):
        xs = [self for self in [1]]
        self.x: int = 1


class CompWalrus:
    def __init__(self):
        xs = [(self := 1) for _ in [1]]
        self.x: int = 1


class GlobalSlots:
    global __slots__
    __slots__ = ("a",)


class GlobalInit:
    global __init__

    def __init__(self):
        self.x: int = 1
