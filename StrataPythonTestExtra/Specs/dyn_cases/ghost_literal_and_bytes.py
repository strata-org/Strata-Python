from typing import Literal

ghost(name="mode", type=Literal["r", "w"])

def read() -> bytes:
    ...
