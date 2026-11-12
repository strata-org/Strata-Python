# field(metadata=...) is not modelled.
from dataclasses import dataclass, field
@dataclass
class P:
    x: int = field(default=0, metadata={"k": 1})
