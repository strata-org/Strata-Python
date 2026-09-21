import servicelib.ParamType


def check_str_arg() -> bool:
    # INVALID: `needs_int` declares `n: int`. Nothing else constrains the call.
    r = servicelib.ParamType.needs_int("hello")
    assert r == r, "a str argument violates the declared parameter type"
    return True
