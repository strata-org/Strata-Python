# The model's own requires would run when g is defined, but PySpec reads @requires as its own form.
import typing
from typing import TypedDict

TD = TypedDict('TD', {'a': int})

def requires(p: int) -> int:
    ...

@requires(lambda kw: True)
def g(**kw: typing.Unpack[TD]) -> None:
    ...
