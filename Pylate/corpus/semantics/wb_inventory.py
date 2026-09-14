# Well-behaved: every partial operation replaced by its total form
# (dict.get with defaults, no bare subscripts on maybe-missing keys),
# so the strict policy has nothing to abort: the analysis is clean with
# zero obligations of the abort kind.
def restock(counts: dict, name: str, amount: int) -> dict:
    current = counts.get(name, 0)
    counts[name] = current + amount
    return counts


def report(counts: dict) -> str:
    parts = []
    for name in counts.keys():
        n = counts.get(name, 0)
        parts.append(name + ":" + str(n))
    return ",".join(parts)


inv = {"bolt": 4}
inv = restock(inv, "bolt", 6)
inv = restock(inv, "nut", 10)
summary = report(inv)
