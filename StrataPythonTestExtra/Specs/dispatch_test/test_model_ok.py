from servicelib.Contract import modeled_text


def check_modeled_text() -> bool:
    value = modeled_text("key")
    assert value is not None, "modeled text must not be None"
    return True
