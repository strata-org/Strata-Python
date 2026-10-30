# After import typing as t, t.Optional[int] reads as Optional[int], through the name that the
# import binds.
import typing as t
from typing import Optional


def f(a: t.Optional[int], b: Optional[int]) -> None:
    ...
