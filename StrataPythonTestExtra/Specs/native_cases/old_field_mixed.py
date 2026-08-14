from typing import Any


@admit(lambda obj, x, result: obj.value >= OLD(x))
def f_ge(obj: Any, x: Any) -> int:
    ...


@admit(lambda obj, x, result: obj.value <= OLD(x))
def f_le(obj: Any, x: Any) -> int:
    ...
