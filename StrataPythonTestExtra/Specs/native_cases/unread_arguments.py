# Arguments that run when the module is imported, but that PySpec doesn't read.
from typing import List

ghost(name="g", type=int, **{"k": 1})

@requires(lambda x: x > 0, **{"k": 1})
def star_star(x: int) -> None:
    ...

@requires(lambda x=1: x > 0)
def positional_default(x: int) -> None:
    ...

@requires(lambda *, x=1: x > 0)
def keyword_default(x: int) -> None:
    ...

@invariant(lambda self: self.n > 0, **{"k": 1})
class C:
    n: int

@admit(lambda x, result: result > 0, 1 // 0)
def extra_argument(x: int) -> int:
    ...

@requires(lambda x: x > 0, lambda y=1: y > 0)
def later_default(x: int) -> None:
    ...

ghost(name="h", type="A" | int)

@ghost(name="k", type="A" | int)
def ghost_type(x: int) -> None:
    ...
