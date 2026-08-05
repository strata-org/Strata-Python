# `is` against the immortal singletons True/False. Python guarantees a unique
# object per singleton, so identity coincides with value here.
def test() -> None:
    a: bool = True
    b: bool = False
    assert (a is True) == True, "a is True"
    assert (a is False) == False, "a is not False"
    assert (b is False) == True, "b is False"
    assert (b is True) == False, "b is not True"
test()
