from dataclasses import dataclass, field
class Desc:
    def __set_name__(self, owner, name):
        print("ev set_name", owner.__name__, name)
    def __repr__(self):
        return 'Desc()'
@dataclass
class D:
    a: object = field(default=Desc())
print(D())
