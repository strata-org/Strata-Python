# The same typing import twice, and a field without a value named like a typing name, bind
# nothing else, so the model translates.
from typing import List
from typing import List


class C:
    List: int

    def m(self, xs: List[int]) -> None:
        ...
