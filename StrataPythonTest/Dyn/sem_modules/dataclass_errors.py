# Errors that @dataclass and field raise while the class is made.
from dataclasses import dataclass, field
def attempt(make):
    try:
        make()
    except (TypeError, ValueError) as e:
        print(type(e).__name__ + ":", e)
def mutable():
    @dataclass
    class A:
        a: list = []
def order():
    @dataclass
    class A:
        a: int = 1
        b: int
def eq_order():
    @dataclass(order=True, eq=False)
    class A:
        a: int
def both():
    field(default=1, default_factory=list)
def no_annotation():
    @dataclass
    class A:
        a = field(default=1)
def frozen_from_plain():
    @dataclass
    class B:
        a: int
    @dataclass(frozen=True)
    class C(B):
        b: int
def plain_from_frozen():
    @dataclass(frozen=True)
    class B:
        a: int
    @dataclass
    class C(B):
        b: int
def overwrite_lt():
    @dataclass(order=True)
    class A:
        a: int
        def __lt__(self, other):
            return True
def overwrite_setattr():
    @dataclass(frozen=True)
    class A:
        a: int
        def __setattr__(self, n, v):
            pass
def overwrite_hash():
    @dataclass(unsafe_hash=True)
    class A:
        a: int
        def __hash__(self):
            return 0
for make in (mutable, order, eq_order, both, no_annotation, frozen_from_plain, plain_from_frozen,
             overwrite_lt, overwrite_setattr, overwrite_hash):
    attempt(make)
