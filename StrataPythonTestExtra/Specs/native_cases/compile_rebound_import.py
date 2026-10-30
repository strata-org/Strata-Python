# A later import of another name as compile replaces re.compile, so the assert is recorded as dropped.
from re import compile

def f(s: str) -> None:
    assert compile("a").search(s) is not None

import re as compile
