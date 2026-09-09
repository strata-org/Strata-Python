# Abort policy, eafp preset (run_all picks it from the _eafp suffix):
# key/value/exhaustion machine raises are modeled, so the except
# KeyError handler below is live EAFP control flow; dispatch-integrity
# categories still abort. Same program as policy_strict.py on purpose.
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
