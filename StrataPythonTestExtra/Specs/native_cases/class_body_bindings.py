# A class body that reads its own bindings, where PySpec reads the module's names instead.
from typing import List

class A:
    ...

class B:
    ...

K = A

class C:
    K = B

    def get(self) -> K:
        ...

    def forward(self) -> "List[K]":
        ...

    def param(self, x: K) -> None:
        ...

    field: K

    def int(self) -> int:
        ...

    def after(self) -> int:
        ...

    class Inner(K):
        ...

    overload = B

    @overload
    def h(self) -> None:
        ...
