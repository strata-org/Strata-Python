from servicelib.Admitted import admitted_value


def check_admitted() -> bool:
    value = admitted_value()
    assert value >= 0, "admitted value must be non-negative"
    return True
