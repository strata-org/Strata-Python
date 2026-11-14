from dataclasses import dataclass
@dataclass
class D:
    a: object
class R:
    def __repr__(self):
        return 'R(' + repr(outer) + ')'
outer = D(None)
inner = D(R())
outer.a = inner
print(repr(outer))
