# A write to an attribute of a function of the model stops with a gap, here a method that
# dataclass generates and dataclasses.field.
import dataclasses
from dataclasses import dataclass


@dataclass
class P:
    x: int


P.__init__.__name__ = "other"
print(P.__init__.__name__)
for f in [P.__init__, dataclasses.field]:
    try:
        f.marker = 1
        print("written", f.marker)
    except AttributeError as e:
        print("AttributeError:", e)
