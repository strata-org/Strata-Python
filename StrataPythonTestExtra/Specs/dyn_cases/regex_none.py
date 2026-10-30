from re import compile

def f(s: str) -> str:
    assert compile("a+").search(s) is None

@admit(lambda s, result: compile("b+").search(result) is None)
def g(s: str) -> str: ...


def h(s: str) -> None:
    assert compile("a+").search(s) != None

def k(s: str) -> None:
    assert compile("a+").search(s) is not None
