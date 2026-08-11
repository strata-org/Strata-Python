import servicelib.Admitted


def check_admitted_value() -> bool:
    value = servicelib.Admitted.admitted_value()
    assert value >= 0, "admitted value must be non-negative"
    return True
