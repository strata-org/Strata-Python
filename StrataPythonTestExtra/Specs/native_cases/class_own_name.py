# Inside its own class statement, a class's name reads the binding that the name had before it.
class TimeoutError(Exception):
    def f(self) -> TimeoutError:
        ...

def D() -> None:
    ...

class D:
    def f(self) -> D:
        ...

class Warning(Exception):
    class Inner:
        def f(self) -> Warning:
            ...

from basetypes import BaseClass

class BaseClass:
    def f(self) -> BaseClass:
        ...
