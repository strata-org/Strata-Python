# `is not` against True/False.
def test() -> None:
    a: bool = True
    assert (a is not False) == True, "a is not False"
    assert (a is not True) == False, "a is True"
test()
