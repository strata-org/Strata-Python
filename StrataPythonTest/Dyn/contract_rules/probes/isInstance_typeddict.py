from typing import TypedDict


class M(TypedDict):
    a: int


x = {"a": 1}
# probe: base.Bool = py.isInstance($x, $M) ^err
# python: isinstance(x, M)
# expect: agree
