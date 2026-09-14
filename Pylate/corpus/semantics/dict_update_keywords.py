"""Every way of adding a key must record it in the key summary.

`annEntailedDeep` reads the key summary to decide a TypedDict's key set is
closed, so a path that adds a key without recording it lets a value claim a
shape it does not have. Three of the four paths recorded it; `update(**kwargs)`
on a plain dict dropped the keys outright, because keyword handling was inside
the `td`-location branch and a dict literal allocates a plain `dict`.

The failure was observable as two spellings of one program disagreeing:
`row["bogus"] = 1` made a later `Row` entailment fail, while
`row.update(bogus=1)` left the value still claiming to satisfy `Row`.
"""
from typing import Required, TypedDict


class Row(TypedDict, total=False):
    name: Required[str]


def takes(row: Row) -> str:
    return row["name"]


def subscript_store() -> int:
    d = {"a": 1}
    d["b"] = 2
    return d["a"]


def update_keywords() -> int:
    d = {"a": 1}
    d.update(b=2)
    return d["a"]


def update_mapping() -> int:
    d = {"a": 1}
    d.update({"b": 2})
    return d["a"]


def setdefault_new() -> int:
    d = {"a": 1}
    d.setdefault("b", 2)
    return d["a"]


def undeclared_via_subscript() -> str:
    row: Row = {"name": "w"}
    row["bogus"] = 1
    return takes(row)


def undeclared_via_update() -> str:
    # Must agree with the line above. It did not.
    row: Row = {"name": "w"}
    row.update(bogus=1)
    return takes(row)


def td_store_subscript(row: Row) -> str:
    # A materialized parameter is a real `td` location, so these two reach
    # `updateTypedDictField` -- which was written three times, and two of the
    # copies dropped the heap write for an undeclared key. Both spellings raise
    # `shape-break`, so the store was flagged either way; what diverged was the
    # heap, and with it the entailment answer at the call below.
    row["bogus"] = 1
    return takes(row)


def td_store_update(row: Row) -> str:
    row.update(bogus=1)
    return takes(row)
