from dataclasses import dataclass
for kw in ({}, {'frozen': True}, {'eq': False}, {'unsafe_hash': True}):
    try:
        @dataclass(**kw)
        class C:
            a: int = 0
            def __hash__(self):
                return 42
        print(kw, C.__hash__(C()) if C.__hash__ is not None else None)
    except TypeError as e:
        print(kw, type(e).__name__, e)
@dataclass
class N:
    a: int = 0
    __hash__ = None
print(N.__hash__)
@dataclass(frozen=True)
class N2:
    a: int = 0
    def __eq__(self, o):
        return True
    __hash__ = None
print(N2.__hash__ is None, callable(N2.__hash__))
