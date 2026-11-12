# @dataclass: __init__, __repr__, __eq__, __doc__, __match_args__, defaults.
from dataclasses import dataclass, field
from typing import List, Optional
def new_list():
    return []
class Foo:
    pass
@dataclass
class P:
    x: int
    y: List[int] = field(default_factory=new_list)
    z: Optional[Foo] = None
    w: "Foo" = 3
p = P(1)
print(p, p == P(1), p == P(2), p != P(1), P.__hash__)
print(P.__doc__, P.__match_args__)
print(P.__init__.__qualname__, P.__init__.__module__, P.__init__.__name__)
print(P(1).y is P(1).y)
for bad in (lambda: P(), lambda: P(1, 2, 3, 4, 5), lambda: P(1, q=2), lambda: P(1, x=1)):
    try:
        bad()
    except TypeError as e:
        print("TypeError:", e)
@dataclass
class Q(P):
    v: int = 7
print(Q(1), Q.__match_args__)
@dataclass
class N:
    """Doc."""
    a: int
print(N.__doc__)
# A generated function's annotations are not modelled.
print(P.__init__.__qualname__, P.__init__.__annotations__)
