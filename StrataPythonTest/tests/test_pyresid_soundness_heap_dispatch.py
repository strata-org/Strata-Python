"""Regression cases for SOUNDNESS_AUDIT.md findings S1-S7."""

from typing import NotRequired, TypedDict


class A:
    def __init__(self, value: int):
        self.x = value


class B:
    def __init__(self, value: int):
        self.x = value


def attribute_union(flag: bool) -> int:
    a = A(1)
    b = B(2)
    target = a if flag else b
    target.x = "changed"
    return a.x + 1


class OptionalCell(TypedDict):
    x: NotRequired[int]


def typed_dict_clear(
    flag: bool, a: OptionalCell, b: OptionalCell
) -> int | None:
    target = a if flag else b
    target.clear()
    return a.get("x")


def typed_dict_update(
    flag: bool, a: OptionalCell, b: OptionalCell
) -> int | None:
    target = a if flag else b
    target.update(x=1)
    return a.get("x")


def typed_dict_setdefault(
    flag: bool, a: OptionalCell, b: OptionalCell
) -> int | None:
    target = a if flag else b
    target.setdefault("x", 1)
    return a.get("x")


class LeftCell(TypedDict):
    left: int


class RightCell(TypedDict):
    right: str


def typed_dict_copy_union(
    flag: bool, left: LeftCell, right: RightCell
) -> str | None:
    target = left if flag else right
    copied = target.copy()
    return copied.get("right")


def primitive_attribute_store(value: int) -> None:
    value.extra = 1


def typed_dict_mapping_update(cell: LeftCell) -> int:
    cell.update({"left": "changed"})
    return cell["left"] + 1
