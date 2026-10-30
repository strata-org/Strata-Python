# An `or` merges into one enum test only when every branch is an enum test on one subject.
def f(x: str, y: str, n: int) -> None:
    assert x == "a" or x == "b", "merged"
    assert x is None or x == "ok", "None or ok"
    assert x != "A" or x == "B", "not A or B"
    assert x == "A" or y == "B" or x == "C", "two subjects"
