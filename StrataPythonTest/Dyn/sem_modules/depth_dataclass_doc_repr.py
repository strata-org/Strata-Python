# An annotation's repr that recurses through the docstring: the small limit agrees, and at the large one
# the rules stop with a gap where CPython raises RecursionError.

from dataclasses import dataclass
n = 0
LIMIT = 10
class R:
    def __repr__(self):
        global n
        n += 1
        if n < LIMIT:
            mk()
        return "R"
def mk():
    @dataclass
    class C:
        x: R() = 1
    return C
def run(limit):
    global n, LIMIT
    n = 0
    LIMIT = limit
    try:
        mk()
        print("ok", n)
    except RecursionError:
        print("rec", n)
run(10)
run(150)
