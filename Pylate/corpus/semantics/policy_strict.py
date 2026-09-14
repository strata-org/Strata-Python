# Abort policy, strict preset (the default): machine raises become
# abort obligations with no exceptional continuation, so the except
# KeyError handler below is dead; the explicit raise in validate is a
# user raise and stays modeled, so its handler is live.
def validate(n: int) -> int:
    if n < 0:
        raise ValueError("negative")
    return n


def lookup(d: dict, k: str) -> int:
    try:
        return d[k]
    except KeyError:
        return 0


def main() -> int:
    d = {"a": 1}
    total = lookup(d, "b")
    try:
        total = total + validate(-1)
    except ValueError:
        total = -1
    return total


r = main()
