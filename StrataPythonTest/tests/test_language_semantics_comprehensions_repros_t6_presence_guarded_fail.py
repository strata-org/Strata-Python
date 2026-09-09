# Negative pair: the guarded branch is reachable and contains a false assertion.
from typing import NotRequired, TypedDict


class Cfg(TypedDict):
    name: str
    retries: NotRequired[int]


def get_cfg() -> Cfg:
    return {"name": "worker", "retries": 3}


def main() -> None:
    cfg = get_cfg()
    if "retries" in cfg:
        retries = cfg["retries"]
        assert retries != retries


main()
