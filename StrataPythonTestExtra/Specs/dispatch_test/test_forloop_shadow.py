xs = ["hello", "world"]
for modeled_text in xs:
    pass
from servicelib.Contract import modeled_text


def use_it() -> str:
    return modeled_text("hello")
