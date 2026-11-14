from dataclasses import dataclass, field
class K:
    def make(self):
        print("ev make")
        return 4
k = K()
@dataclass
class D:
    a: int = field(default_factory=k.make)
print(D())
