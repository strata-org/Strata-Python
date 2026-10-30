# The stubs' @requires preconditions reach the dispatch extern, each guarded by its literal.
from typing import Literal, overload

@overload
@requires(lambda name, region: len(region) >= 3)
def connect(name: Literal["a"], region: str) -> int:
    ...

@overload
@requires(lambda name, region: len(region) >= 5)
def connect(name: Literal["b"], region: str) -> str:
    ...
