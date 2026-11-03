# This call changes what `typing.Unpack` is, so PySpec can't read the model below it.
import typing
from typing import TypedDict

TD = TypedDict('TD', {'a': int})

setattr(typing, "Unpack", dict)

def f(**kw: typing.Unpack[TD]) -> None:
    ...
