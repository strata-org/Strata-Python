from typing import TypedDict


class Branch:
    b: int

    def __init__(self, b: int):
        self.b = b


class Root:
    a: Branch

    def __init__(self, a: Branch):
        self.a = a


class Record:
    field: int

    def __init__(self, field: int):
        self.field = field


class Records(TypedDict):
    key: Record


def combine(x: Root, d: Records) -> int:
    return x.a.b + d["key"].field
