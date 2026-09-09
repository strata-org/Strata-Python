# Control for t5: the SAME optional key, but guarded by `in`.
# If the model tracked presence, the guard would discharge the obligation and
# the read inside the branch would be provably safe. If there is no presence
# predicate at all, guarded and unguarded look identical.
from typing import TypedDict, NotRequired


class Cfg(TypedDict):
    name: str
    retries: NotRequired[int]


def get_cfg() -> Cfg:
    return {"name": "worker"}


def main() -> None:
    c = get_cfg()
    if 'retries' in c:
        r = c['retries']   # guarded: must be safe
        assert r == r


main()
