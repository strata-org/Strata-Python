# Declared shapes of plain classes: each class body's function states its fields with their
# annotations and defaults, as written: a ClassVar too, a private name mangled, a conditional
# one too, and those an __init__ declares as self.x: T, each pointing to its __init__,
# mangled, conditional under an if, but not in a nested function, in a generator __init__,
# a stub, or in an __init__ that rebinds self.  __slots__ is stated as its
# value.
from typing import ClassVar, Optional as Opt


class Point:
    dims: ClassVar[int] = 2
    x: int
    y: "Opt[int]"
    parent: Opt["Point"] = None
    __tag: str = ""
    if dims:
        z: float = 0.0

    def __init__(self, x, y):
        self.x = x
        self.y, (self.z, self.__tag) = y, (0.0, "p")
        self.x += 1

        def later():
            self.w = 1
        later()


class Slotted:
    __slots__ = ("a", "b")

    def __init__(this, a):
        this.a = a


class Bare:
    pass


class Box:
    size: int = 0

    def __init__(self, items):
        self.items: list[str] = items
        self.count: int
        if items:
            self.first: str = items[0]


flag = True


class More:
    if flag:
        def __init__(self):
            self.__hidden: int = 1

            def later():
                self.w: int = 2
            later()


class GenInit:
    def __init__(self):
        self.g: int = 1
        yield


class Conn:
    if flag:
        def __init__(self):
            self.buf: bytes = b""
    else:
        def __init__(self):
            self.lines: list[str] = []


class Rb:
    def __init__(self, other):
        self = other
        self.x: int = 1
