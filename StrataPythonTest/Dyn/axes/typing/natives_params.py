from dataclasses import dataclass, field, MISSING
@dataclass(order=True, frozen=True)
class D:
    a: int
    b: list = field(default_factory=list)
print(repr(D.__dataclass_params__))
print(sorted(D.__dataclass_fields__))
f = D.__dataclass_fields__['b']
print(f.name, f.default is MISSING, f.default_factory is list, repr(f._field_type))
print(type(MISSING).__name__)
