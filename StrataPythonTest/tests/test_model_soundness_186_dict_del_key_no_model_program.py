# `del d[key]` — no `DictStrAny_del` operation; key removal from association
# list unimplemented
"""
`del d[key]` removes a key from a dict. Under pure association-list
semantics, this requires producing a new dict without that key.

But `DictStrAny` is an association list that PREPENDS on set:
  DictStrAny_set(d, k, v) = DictStrAny_cons(k, v, d)

There is likely no `DictStrAny_del` operation. And even if there were,
the association list may have MULTIPLE entries for the same key (from
overwrites — finding 082). Deletion must remove ALL entries for that key.

Additionally, `del d[key]` raises KeyError if key is absent.
The model must either check presence first or produce an exception.

Uses ONLY confirmed-accepted constructs: dict, del, str, int, function def.
"""


def delete_existing_key() -> dict[str, int]:
    d: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    del d["b"]
    return d  # {"a": 1, "c": 3}


def delete_and_check_len() -> int:
    d: dict[str, int] = {"x": 10, "y": 20, "z": 30}
    del d["y"]
    return len(d)  # 2


def delete_and_check_membership() -> bool:
    d: dict[str, int] = {"name": 1, "age": 2}
    del d["age"]
    return "age" in d  # False


def delete_then_readd() -> int:
    d: dict[str, int] = {"k": 100}
    del d["k"]
    d["k"] = 200
    return d["k"]  # 200


def delete_raises_keyerror() -> int:
    """del d[missing_key] raises KeyError in CPython."""
    d: dict[str, int] = {"a": 1}
    try:
        del d["nonexistent"]
        return 0  # never reached
    except KeyError:
        return -1


def main() -> None:
    # Delete existing
    result: dict[str, int] = delete_existing_key()
    assert "a" in result
    assert "b" not in result
    assert "c" in result

    # Length decreases
    assert delete_and_check_len() == 2

    # Membership after delete
    assert delete_and_check_membership() == False

    # Delete then re-add
    assert delete_then_readd() == 200

    # KeyError on missing
    assert delete_raises_keyerror() == -1

    print(len(delete_existing_key()), delete_and_check_len(),
          delete_then_readd())


main()
