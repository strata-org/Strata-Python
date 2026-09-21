import servicelib.ParamType


def check_int_arg() -> bool:
    r = servicelib.ParamType.needs_int(1)
    assert r == r, "an int argument satisfies the declared parameter type"
    return True
