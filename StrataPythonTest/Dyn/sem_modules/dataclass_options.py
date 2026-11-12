# @dataclass options: frozen, order, eq, unsafe_hash, init, repr, kw_only.
from dataclasses import dataclass, field, FrozenInstanceError
@dataclass(frozen=True)
class F:
    a: int
f = F(1)
try:
    f.a = 2
except FrozenInstanceError as e:
    print(type(e).__name__, isinstance(e, AttributeError), e)
try:
    del f.a
except FrozenInstanceError as e:
    print(e)
print(f.__hash__() == (1,).__hash__(), {f: 1}[F(1)])
@dataclass(order=True)
class V:
    major: int
    minor: int
print(V(1, 2) < V(1, 3), V(2, 0) > V(1, 9), V(1, 1) <= V(1, 1), V(2, 0) > V(1, 5))
try:
    V(1, 2) < 3
except TypeError as e:
    print("TypeError:", e)
@dataclass(eq=False)
class E:
    a: int
print(E(1) == E(1), E.__hash__ is object.__hash__)
@dataclass(unsafe_hash=True)
class U:
    a: int
print(U(1).__hash__() == (1,).__hash__(), {U(1): 2}[U(1)])
@dataclass(init=False, repr=False)
class I:
    a: int = 0
print(I().a, I.__doc__)
@dataclass(kw_only=True)
class K:
    a: int
    b: int = 0
print(K(a=1))
try:
    K(1)
except TypeError as e:
    print("TypeError:", e)
@dataclass
class C:
    a: int
    b: int = field(default=2, repr=False, compare=False)
print(C(1), C(1, 3) == C(1, 4))
