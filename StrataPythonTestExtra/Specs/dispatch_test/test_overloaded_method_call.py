from servicelib.Overloaded import make_p


def call_overloaded() -> None:
    p = make_p()
    r = p.m(1)
    assert r == 7, "r is 7"
