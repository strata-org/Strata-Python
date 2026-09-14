"""Entailment against union and TypedDict annotations, both directions.

Nothing pinned the *negative* side of this -- that a valid argument produces no
obligation -- so two rules could reject every valid value unnoticed. Unions were
checked as "the whole value entails one member", which no union value can
satisfy: `int | None` is `{int, none}`, which entails neither member alone.
TypedDicts were checked nominally against a `td` location, but a dict literal
allocates a plain `dict`, so a locally built row failed with every key present.

Both were invisible while a failed check was a soft obligation. They became
aborts when the call site started enforcing annotations, which is how they
surfaced.
"""
from typing import NotRequired, Required, TypedDict


class A:
    def m(self) -> int:
        return 1


class B:
    def m(self) -> int:
        return 2


class Row(TypedDict, total=False):
    name: Required[str]
    count: int
    note: NotRequired[str]


def takes_union(v: A | B) -> int:
    return v.m()


def takes_optional(n: int | None) -> int:
    return 0 if n is None else n


def takes_row(row: Row) -> str:
    return row["name"]


# --------------------------------------------------------------- satisfied

def union_both_members(flag: bool) -> int:
    v = A() if flag else B()
    return takes_union(v)


def union_one_member() -> int:
    return takes_union(A())


def optional_both() -> int:
    return takes_optional(None) + takes_optional(1)


def row_required_only() -> str:
    row: Row = {"name": "w"}
    return takes_row(row)


def row_every_key() -> str:
    row: Row = {"name": "w", "count": 1, "note": "n"}
    return takes_row(row)


# ---------------------------------------------------------------- violated
#
# All four abort. Only the first reports the *definite* breach, though the three
# shape failures are just as definite: `assumeAnn` narrows by tag, and all four
# of these are `dict`, so the surviving slice is non-empty and the split reads
# them as partial. The enforcement is unaffected -- the abort fires either way --
# but the extra hard obligation that says "no caller could satisfy this" needs a
# shape-aware narrowing to fire here.

def optional_wrong_type() -> int:
    return takes_optional("s")


def row_missing_required() -> str:
    row: Row = {"count": 1}
    return takes_row(row)


def row_wrong_field_type() -> str:
    row: Row = {"name": 1}
    return takes_row(row)


def row_undeclared_key() -> str:
    row: Row = {"name": "w", "other": 1}
    return takes_row(row)
