from typing import Any, Union

Number = Union[int, float]

def f(x: Any) -> None:
    assert isinstance(x, Number)
