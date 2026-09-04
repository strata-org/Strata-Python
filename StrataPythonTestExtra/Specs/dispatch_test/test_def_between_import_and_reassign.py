from servicelib.Contract import modeled_text


def use_y() -> str:
    return modeled_text("hello")


modeled_text = 42
