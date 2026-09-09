# A literal-key store records a per-key cell, so a later read can prove the key
# present. The weak and joined cases must not: CPython raises KeyError from
# conditional_store(False, n) and from summary_store([]), and a store on one
# branch of an `if` must not read back as proof of presence after the join.
def strong_store(n: int) -> int:
    d = {}
    d["k"] = n
    return d["k"]


def conditional_store(flag: bool, n: int) -> int:
    d = {}
    if flag:
        d["k"] = n
    return d["k"]


def summary_store(items: list[int]) -> int:
    box = {}
    for x in items:
        holder = {}
        holder["k"] = x
        box = holder
    return box["k"]
