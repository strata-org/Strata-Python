# The other bindings of a class body, in source order, each with its value or its kind: the
# members of an Enum, the _fields_ of a ctypes structure, a Pydantic model_config, a method.
# A chained assignment binds each name; an unpacked one each name of the target; an
# augmented one is marked, and so is one under a compound statement; an import, a for, a
# with, an except, a del and an assignment expression bind a name of their kind, the last one
# before its statement's own bindings, wherever it is in an expression.  An except's name is
# unbound after its handler.  A binding that may not run is marked: a for target, the
# bindings of an except handler, and an assignment expression after a short circuit.  A field and the assignment statements
# to __slots__ are stated elsewhere, but another name bound with __slots__ is here.  A private
# name is mangled; a name declared global or nonlocal is bound outside the class and left
# out.  Operators keep their operands, and only a chain of | is one union.  A match's
# captures are not listed: the translator rejects the statement.
import ctypes
from enum import Enum
from pydantic import BaseModel, ConfigDict

flag = True


class Status(Enum):
    PENDING = 1
    RUNNING = -2
    DONE = (3, "done")


class Registers(ctypes.Structure):
    _fields_ = [("status", ctypes.c_int), ("buffer", ctypes.c_char * 10)]


class Product(BaseModel):
    model_config = ConfigDict(frozen=True)
    sku: str

    def total(self):
        return 0


class Kinds:
    a = b = 1
    c, (d, *e) = 1, (2, 3)
    a += 1
    __slots__ = s = ("x",)
    (f): int = 2
    import os.path
    from os import sep as separator
    for i in range(2):
        j = i
    with open("f") as fh:
        pass
    try:
        k = 1
    except ValueError as err:
        pass
    del k
    m = (n := 4) + 1
    if flag:
        w = 5
    __p = 6
    q = -a + ~b - (not c) * d ** 2

    class Inner:
        z = 7


def f(*a, **k):
    return 0


class Walrus:
    d = {(a := 1): (b := 2), **(c := {}), (dd := 3): 4}
    x = f(k=(k1 := 1), *[(p1 := 2)])
    y = (p := 1) if (q := 0) else (r := 2)
    s = [1, 2][(lo := 0):(hi := 1):(st := 1)]
    fs = f"{(fv := 1)}{2:{(spec := '')}}"
    lam = lambda a=(ld := 1), *, b=(lk := 2): (lb := 3)
    cmp = (c1 := 1) < (c2 := 2) < (c3 := 3)
    t = (t1 := 1), *[(t2 := 2)]
    st2 = {(s1 := 1)}
    at = (o := f).__name__
    sub = (sv := [1])[(si := 0)]
    un = -(u := 1)
    assert (as1 := 1), (as2 := "m")
    del (dl := [1])[0]
    sc = 0 or (sc1 := 1) and (sc2 := 2)

    @(dec := lambda g: g)
    def m(self, v=(dv := 1)) -> (ra := int):
        pass

    class Inner((base := object), metaclass=(mt := type)):
        pass

    with open("f") as (wv := [0])[0]:
        pass
    for fv2 in (it := []):
        pass


class Handlers:
    try:
        raise ValueError
    except (E := ValueError) as err:
        err = 5
    for k in []:
        pass


class Flags:
    R = 1
    W = 2
    RW = R | W
    RWX = R | (W | 4)


def outer():
    v = 0

    class Uses:
        global flag
        nonlocal v
        flag = False
        v = 1
        u = 2
    return Uses


class Rejected:
    match 1:
        case x:
            pass
