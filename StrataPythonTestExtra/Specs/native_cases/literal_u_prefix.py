# A `u` prefix on a string changes nothing: `Literal[u"a"]` is `Literal["a"]`.
from typing import Literal

def f(x: Literal[u"a"]) -> None:
    ...
