"""Paired defect benchmark: for each defect class, ok_<name> works and
bug_<name> plants one defect.  Units take one int parameter; CASES lists the
concrete arguments the evaluator runs (chosen so every planted defect fires
on at least one argument)."""


from typing import TypedDict


class Movie(TypedDict):
    title: str
    year: int


class Circle:
    def __init__(self, r: int):
        self.r = r

    def area(self) -> int:
        return self.r * self.r


class Square:
    def __init__(self, s: int):
        self.s = s

    def area(self) -> int:
        return self.s * self.s


class Robot:
    def __init__(self):
        self.serial = 1


class GoodBox:
    def __init__(self, k: int):
        self.a = 1
        self.b = 2


class BugBox:
    def __init__(self, k: int):
        self.a = 1
        if k:
            self.b = 2


class Acc:
    total: int

    def __init__(self):
        self.total = 0


def helper(n: int) -> int:
    return n + 1


def ok_dispatch(k: int) -> int:
    acc = 0
    for x in [Circle(2), Square(3)]:
        acc = acc + x.area()
    return acc


def bug_dispatch(k: int) -> int:
    acc = 0
    for x in [Circle(2), Robot()]:
        acc = acc + x.area()
    return acc


def ok_none(k: int) -> int:
    x = Circle(2) if k else None
    if x is not None:
        return x.area()
    return 0


def bug_none(k: int) -> int:
    x = Circle(2) if k else None
    return x.area()


def ok_init(k: int) -> int:
    b = GoodBox(k)
    return b.a + b.b


def bug_init(k: int) -> int:
    b = BugBox(k)
    return b.a + b.b


def ok_tdkey(k: int) -> int:
    m = Movie(title="Alien", year=1979)
    return m["year"]


def bug_tdkey(k: int) -> int:
    m = Movie(title="Alien", year=1979)
    return m["director"]


def bug_dkey(k: int) -> int:
    d = {"a": 1}
    return d["b"]


def ok_idx(k: int) -> int:
    xs = [1, 2, 3]
    return xs[0]


def bug_idx(k: int) -> int:
    xs = [1, 2, 3]
    return xs[5]


def ok_add(k: int) -> int:
    s = 1 if k else 0
    return s + 1


def bug_add(k: int) -> int:
    s = "n" if k else 0
    return s + 1


def ok_unbound(k: int) -> int:
    if k:
        z = 1
    else:
        z = 2
    return z


def bug_unbound(k: int) -> int:
    if k:
        z = 1
    return z


def ok_ann(k: int) -> int:
    return helper(k)


def bug_ann(k: int) -> int:
    return helper("s")


def ok_fann(k: int) -> int:
    a = Acc()
    a.total = 5
    return a.total + 1


def bug_fann(k: int) -> int:
    a = Acc()
    a.total = "x"
    return a.total + 1


def risky(k: int) -> int:
    if k:
        raise KeyError("nope")
    return 1


def ok_catch(k: int) -> int:
    try:
        return risky(k)
    except KeyError:
        return 0


def bug_catch(k: int) -> int:
    try:
        return risky(k)
    except ValueError:
        return 0


def ok_hash(k: int) -> int:
    pts = {(1, 2), (3, 4)}
    return len(pts)


def bug_hash(k: int) -> int:
    rows = {Movie(title="a", year=1), Movie(title="b", year=2)}
    return len(rows)


def gsrc(k: int):
    yield 1
    yield 2


def ok_gen(k: int) -> int:
    it = gsrc(k)
    acc = 0
    while True:
        try:
            x = next(it)
        except StopIteration:
            break
        acc = acc + x
    return acc


def bug_gen(k: int) -> int:
    it = gsrc(k)
    a = next(it)
    b = next(it)
    c = next(it)
    return a + b + c


CASES = {name: [0, 1] for name in [
    "ok_dispatch", "bug_dispatch", "ok_none", "bug_none", "ok_init",
    "bug_init", "ok_tdkey", "bug_tdkey", "bug_dkey", "ok_idx", "bug_idx", "ok_add",
    "bug_add", "ok_unbound", "bug_unbound", "ok_ann", "bug_ann", "ok_fann",
    "bug_fann", "ok_catch", "bug_catch", "ok_gen", "bug_gen", "ok_hash", "bug_hash"]}
