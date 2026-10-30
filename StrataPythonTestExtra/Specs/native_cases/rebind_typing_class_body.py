# A class body that binds a name from typing rejects the model.
from typing import List


class C:
    List = int

    def m(self, xs: List[int]) -> None:
        ...
