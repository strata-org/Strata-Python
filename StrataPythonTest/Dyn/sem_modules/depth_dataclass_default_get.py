# A default's __get__ that recurses through @dataclass: the small limit agrees, and at the large one
# the rules stop with a gap where CPython raises RecursionError.

from dataclasses import dataclass
n = 0
LIMIT = 10
class D:
    def __get__(self, obj, owner):
        global n
        n += 1
        if n < LIMIT:
            mk()
        return 1
def mk():
    @dataclass
    class C:
        x: int = D()
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
run(170)
