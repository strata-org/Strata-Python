from dataclasses import dataclass
class Desc:
    def __set_name__(self, owner, name):
        print("set_name", owner.__name__, name)
    def __get__(self, obj, t=None):
        return 5
    def __repr__(self):
        return 'Desc()'
@dataclass
class D:
    a: int = Desc()
print(D(), D(3))
