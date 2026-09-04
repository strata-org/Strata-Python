from servicelib.Contract import modeled_text
from nonexistent_module import modeled_text


def use_it() -> str:
    return modeled_text("hello")
