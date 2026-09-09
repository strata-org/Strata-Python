# `isinstance(d["key"], int)` narrows `d["key"]` to `int`. Then `d["key"] =
# "changed"` assigns `str` to the same subscript. Mypy does NOT invalidate the
# narrowing — `reveal_type(d["key"])` still shows `int` after the assignment.
"""
a36_dict_subscript_narrowing.py — isinstance narrowing on d["key"] not invalidated by d["key"] = str.

mypy narrows d["key"] to int via isinstance. Then d["key"] = "changed" assigns str.
mypy does NOT invalidate the narrowing — it still thinks d["key"] is int.
Subsequent use of d["key"] as int produces TypeError.

This is NOT a method-call invalidation bug. It's a DIRECT ASSIGNMENT to the
same subscript expression that was narrowed. mypy's binder doesn't track that
d["key"] = x invalidates isinstance(d["key"], int).

mypy --strict: Success (0 errors)
Runtime: TypeError — str - int
"""


def main() -> None:
    d: dict[str, int | str] = {"key": 42}
    if isinstance(d["key"], int):
        d["key"] = "changed"  # direct assignment to narrowed subscript
        # mypy: d["key"] is still int (narrowing not invalidated!)
        result: int = d["key"] - 1  # TypeError: str - int


if __name__ == "__main__":
    main()
