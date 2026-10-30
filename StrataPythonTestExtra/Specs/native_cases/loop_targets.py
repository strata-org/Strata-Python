# A loop's target counts as rebound only after the loop, and a loop whose body has a statement
# that PySpec skips has every assert recorded as dropped.
from typing import List

def after_loop(x: int, xs: List[int]) -> None:
    for x in xs:
        assert x >= 0, "each x is not negative"
    assert x >= 1, "x is positive"

def if_in_for(xs: List[int]) -> None:
    for x in xs:
        if x > 0:
            assert x < 10, "x is small"

def nested_for(rows: List[List[int]]) -> None:
    for row in rows:
        for x in row:
            assert x >= 0, "x is not negative"

def inner_shadow(xs: List[int], ys: List[int]) -> None:
    for x in xs:
        for x in ys:
            pass
        assert x > 0, "x is positive"

def loop_carried(n: int, xs: List[int]) -> None:
    for x in xs:
        assert n > 0, "n is positive"
        n = n - 1

def loop_var_rebound(xs: List[int]) -> None:
    for x in xs:
        x = x - 1
        assert x > 0, "x is positive"

def untranslated_if_in_loop(xs: List[int]) -> None:
    for x in xs:
        assert x > 0, "x is positive"
        if x.bit_length() > 3:
            pass

def nested_taint(n: int, rows: List[List[int]]) -> None:
    for row in rows:
        assert n > 0, "n is positive"
        for x in row:
            n = n - 1

def sibling_loops(a: List[int], b: List[int]) -> None:
    for item in a:
        assert item >= 1, "each a is positive"
    for item in b:
        assert item >= 0, "each b is not negative"

def unicode_name(x: int, xs: List[int]) -> None:
    for x in xs:
        pass
    assert ｘ > 0, "x is positive"

def builtin_target(s: str, ns: List[int]) -> None:
    for len in ns:
        pass
    assert len(s) >= 1, "s is not empty"

def type_target(s: str, ns: List[int]) -> None:
    for str in ns:
        pass
    assert isinstance(s, str), "s is a str"


def inner_rebinds_before(y: int, xs: List[int], ys: List[int]) -> None:
    for x in xs:
        assert y > 0, "y is positive"
        for y in ys:
            pass

def if_rebinds_before(y: int, xs: List[int], ys: List[int]) -> None:
    for x in xs:
        assert y > 0, "y is positive"
        if x > 0:
            for y in ys:
                pass


def iterable_rebound_later(xs: List[int], ys: List[int], zs: List[List[int]]) -> None:
    for x in xs:
        for y in ys:
            assert y > 0, "each y is positive"
        for ys in zs:
            pass

def condition_rebound_later(n: int, xs: List[int], ns: List[int]) -> None:
    for x in xs:
        if n > 0:
            assert x > 0, "x is positive"
        for n in ns:
            pass
