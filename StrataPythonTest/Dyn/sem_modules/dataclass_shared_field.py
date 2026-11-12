# One Field object for two annotations: the field is keyed by its last name.
from dataclasses import dataclass, field
f = field(default=3)
@dataclass
class A:
    x: int = f
    y: int = f
print(A())
print(A.__match_args__, len(A.__dataclass_fields__), type(A.__dict__["x"]).__name__)
