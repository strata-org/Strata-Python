from typing import overload

# A contract on an @overload stub of a method is rejected: the stub gets no Laurel
# procedure, so the contract would be dropped.
class P:
    @overload
    @requires(lambda x: x >= 0)
    @ensures(lambda result: result >= 0)
    @admit(lambda x, result: result == 7)
    @modifies(lambda x: x)
    @ghost(name="g")
    def m(self, x: int) -> int:
        ...

    @overload
    def m(self, x: str) -> int:
        ...
