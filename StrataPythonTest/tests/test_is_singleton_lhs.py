# Python allows the singleton on the left as well.
def test() -> None:
    a: bool = True
    assert (True is a) == True, "singleton on the left"
    assert (None is None) == True, "None is None"
    assert (False is a) == False, "False is not a"
test()
