# A field name that collides with the generated source's own names.
from dataclasses import dataclass
@dataclass(frozen=True)
class C:
    __dataclass_builtins_object__: object
try:
    print(C(5))
except TypeError as e:
    print("TypeError", e)
