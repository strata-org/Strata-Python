# The three arithmetic unary operators. `+x` is not the identity and `~x` is
# not defined on inexact numbers; both were previously erased or rejected.
class Meter:
    v: int

    def __init__(self, v: int):
        self.v = v

    def __neg__(self) -> int:
        return -self.v

    def __pos__(self) -> int:
        return self.v


def neg_int(x: int) -> int:
    return -x

def pos_int(x: int) -> int:
    return +x

def inv_int(x: int) -> int:
    return ~x

def inv_float(x: float) -> int:
    return ~x

def pos_str(s: str) -> str:
    return +s

def neg_obj(m: Meter) -> int:
    return -m

def pos_obj(m: Meter) -> int:
    return +m

def inv_obj(m: Meter) -> int:
    return ~m
