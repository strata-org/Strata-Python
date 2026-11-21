from servicelib.Contract import modeled_text


def helper() -> bool:
    value = modeled_text("key")
    assert value is not None, "helper body check"
    return True


def check_helper() -> bool:
    helper()
    return True
