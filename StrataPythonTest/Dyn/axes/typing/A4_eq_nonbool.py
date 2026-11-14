from dataclasses import dataclass
@dataclass
class D:
    a: object
    b: object
class B:
    def __bool__(self):
        print("ev bool")
        raise ValueError('bool')
class E:
    def __eq__(self, o):
        return B()
    __hash__ = object.__hash__
try:
    print(D(E(), 1) == D(E(), 1))
except Exception as e:
    print(type(e).__name__, e)
