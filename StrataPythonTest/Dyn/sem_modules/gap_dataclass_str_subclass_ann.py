# An annotation that is an instance of a str subclass: isinstance(annotation, str) passes, and
# the checks of ClassVar, InitVar and KW_ONLY read its value.
import dataclasses
import typing
from dataclasses import dataclass
class S(str):
    pass
@dataclass
class C:
    x: S("typing.ClassVar") = 1
print(C())

@dataclass
class K:
    a: S("dataclasses.KW_ONLY")
    b: int = 1
print(K(b=2))
