# Classes whose metaclass defines __eq__ and __hash__ can be == while distinct, which CPython's
# typing cache honours: such a class is not a known value, so the subscription stops with a gap.
from typing import List
class M(type):
    def __eq__(s, o): return True
    def __hash__(s): return 0
class A(metaclass=M): pass
class B(metaclass=M): pass
x = List[A]
y = List[B]
print(x is y, y.__args__[0].__name__)
