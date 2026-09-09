# TypedDict with NotRequired: does the frontend model key PRESENCE?
from typing import TypedDict, NotRequired


class Cfg(TypedDict):
    name: str            # required
    retries: NotRequired[int]   # optional


def get_cfg() -> Cfg:
    return {"name": "worker", "retries": 3}


def main() -> None:
    c = get_cfg()
    # 'name' is REQUIRED, so this read must be safe (no KeyError obligation).
    n = c['name']
    assert len(n) >= 0
    # 'retries' is OPTIONAL: an unguarded read SHOULD raise a KeyError obligation.
    r = c['retries']
    assert r == r


main()
