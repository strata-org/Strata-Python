import servicelib.Counter


def check_modeled_value() -> bool:
    value = servicelib.Counter.modeled_value()
    assert value is None, "modeled value must be None"
    return True
