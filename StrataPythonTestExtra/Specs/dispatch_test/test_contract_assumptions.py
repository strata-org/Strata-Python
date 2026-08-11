import servicelib.Contract


def check_modeled_text() -> bool:
    value = servicelib.Contract.modeled_text("key")
    assert value is not None, "modeled text must not be None"
    return True
