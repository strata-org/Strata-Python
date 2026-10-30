from typing import Union

class Box:
    n: int

ghost(name="g", type=Union[Box, None], init=None)

@modifies(lambda: g.n)
def bump() -> None:
    ...
