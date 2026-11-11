# A write to an attribute of typing's functions stops with a gap.
import typing
from typing import TypedDict
typing.cast.__name__ = "other"
print(typing.cast.__name__)
TypedDict.__name__ = "Other"
print(TypedDict.__name__)
try:
    typing.cast.foo = 2
    print("written", typing.cast.foo)
except AttributeError as e:
    print("AttributeError:", e)
