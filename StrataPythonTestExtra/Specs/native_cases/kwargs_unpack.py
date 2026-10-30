# `**kw: Unpack[TD]` describes the keyword arguments together; `**kw: TD` describes each value.
# `typing.Unpack[TD]` and `t.Unpack[TD]` are `Unpack[TD]` too.
import typing
import typing as t
from typing import TypedDict, Unpack

TD = TypedDict('TD', {'a': int})

def f(**kw: Unpack[TD]) -> None:
    ...

def g(**kw: TD) -> None:
    ...

def h(**kw: typing.Unpack[TD]) -> None:
    ...

def k(**kw: t.Unpack[TD]) -> None:
    ...
