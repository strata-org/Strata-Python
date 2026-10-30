from typing import overload


# A model class with an overloaded __init__. The overload stubs get no Laurel
# procedure, so the model loads.
class O:
    @overload
    def __init__(self, x: int) -> None:
        ...

    @overload
    def __init__(self, x: str) -> None:
        ...

    def m(self) -> None:
        ...


def make_o() -> O:
    ...


# A model class with an overloaded method and no contract on it. A call of the
# method checks nothing and assumes nothing about its result.
class P:
    @overload
    def m(self, x: int) -> int:
        ...

    @overload
    def m(self, x: str) -> int:
        ...


def make_p() -> P:
    ...
