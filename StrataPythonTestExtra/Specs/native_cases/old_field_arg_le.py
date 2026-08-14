from typing import Any


@admit(lambda obj, result: obj.value <= OLD(obj.value))
def f(obj: Any) -> int:
    ...
