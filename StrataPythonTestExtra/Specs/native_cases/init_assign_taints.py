# A top-level assignment of __init__ makes a later assert's meaning unknown.
from typing import List

class C:
    def __init__(self, xs: List[int]) -> None:
        xs = []
        assert len(xs) >= 1, "xs is not empty"
