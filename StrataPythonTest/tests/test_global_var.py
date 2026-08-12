G: int = 100
H: int = G + 23


def test_global_var():
    assert G == 100, "global variable"
    assert H == 123, "module initialization order"


def read_later_global() -> int:
    return LATER


LATER: int = 7


test_global_var()
assert read_later_global() == 7, "function resolves a later module assignment"
