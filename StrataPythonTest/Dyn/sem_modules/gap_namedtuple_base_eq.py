# A base before NamedTuple whose == is a user method.
from typing import NamedTuple
class U:
    def __mro_entries__(self, bases):
        return ()
    def __eq__(self, o):
        print("eq called")
        return False
    __hash__ = object.__hash__
class P(U(), NamedTuple):
    x: int
print(P(1))
