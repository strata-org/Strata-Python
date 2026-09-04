xs: list = ["hello"]
from servicelib.Contract import modeled_text
if len(xs) > 0:
    modeled_text = 42


def use_it() -> object:
    return modeled_text
