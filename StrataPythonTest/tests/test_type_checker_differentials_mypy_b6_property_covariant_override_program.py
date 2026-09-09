# Child overrides Base's `@property` with a narrower return type (`int` vs
# `int|str`) and a narrower setter parameter type. A function accepting `Base`
# writes `str` via `b.x = "hello"` — mypy checks against Base's setter
# (accepts `int|str`), passes. At runtime, Python dispatches to Child's setter
# (MRO), which stores the str in `self._x` despite the `int` annotation.
# Child's getter then returns str, but mypy thinks it returns int.
"""
b6_property_covariant_override.py — Property return type narrowed in subclass; write through base.

Child overrides Base's @property with a narrower return type (int vs int|str).
A function accepting Base writes str via the property setter.
Python dispatches to Child's setter (MRO), which receives str despite
being annotated for int. The backing field becomes str.
Child's getter returns str, but mypy thinks it returns int.

mypy --strict: Success (0 errors)
Runtime: TypeError — str + int
"""


class Base:
    def __init__(self) -> None:
        self._x: int | str = 42

    @property
    def x(self) -> int | str:
        return self._x

    @x.setter
    def x(self, val: int | str) -> None:
        self._x = val


class Child(Base):
    def __init__(self) -> None:
        self._x: int = 42

    @property
    def x(self) -> int:
        return self._x

    @x.setter
    def x(self, val: int) -> None:
        self._x = val


def corrupt(b: Base) -> None:
    b.x = "hello"  # mypy: Base.x.setter accepts int|str. OK.
    # Runtime: Child.x.setter is called (MRO). Receives "hello" (str).
    # Child._x becomes "hello" despite being annotated int.


def main() -> None:
    c = Child()
    corrupt(c)  # passes Child as Base, writes str via property
    result: int = c.x + 1  # mypy: int + int. Runtime: str + int → TypeError


if __name__ == "__main__":
    main()
