# Optional[T] means Union[T, None], also with the module prefix.
import typing
from typing import Optional, Union


def f(a: Optional[str], b: typing.Optional[int], c: Union[str, None], d: typing.Union[int, None]) -> Optional[str]:
    ...


def g(xs: typing.List[str], m: typing.Dict[str, int]) -> None:
    ...
