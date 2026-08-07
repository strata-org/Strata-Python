# The distinction `is` must preserve: `True == 1` is true (numeric equality)
# but `True is 1` is false (different objects). Guards against lowering `is`
# to PEq, which normalizes bool into int.
def test() -> None:
    a: bool = True
    b: int = 1
    assert (a == b) == True, "True equals 1"
    assert (a is True) == True, "but a is the True singleton"
    assert (b is True) == False, "and 1 is not the True singleton"
test()
