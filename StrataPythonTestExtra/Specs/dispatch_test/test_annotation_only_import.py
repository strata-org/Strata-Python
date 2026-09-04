from typing import Any

modeled_text: Any
from servicelib.Contract import modeled_text


def use_it() -> str:
    return modeled_text("hello")
