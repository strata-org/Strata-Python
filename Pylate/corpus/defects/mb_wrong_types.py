# Badly behaved, inside the fragment: type-confused operations the
# dispatch table proves wrong for every run. Under the strict policy
# each is a guaranteed abort row (dispatch category), not a modeled
# exception: adding int to str, calling a method on None, and calling
# an attribute that no class on the receiver has.
class Point:
    def __init__(self, x: int):
        self.x = x


def mix(n: int, s: str):
    return n + s


def poke(p):
    q = None
    q.wiggle()
    return p


pt = Point(3)
bad1 = mix(1, "one")
bad2 = pt.missing_method()
bad3 = poke(pt)
