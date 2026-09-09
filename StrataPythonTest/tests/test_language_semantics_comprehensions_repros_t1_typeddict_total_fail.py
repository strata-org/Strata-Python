# Negative pair: an unguarded absent NotRequired key raises KeyError.
from typing import NotRequired, TypedDict


class Cfg(TypedDict):
    name: str
    retries: NotRequired[int]


def get_cfg() -> Cfg:
    return {"name": "worker"}


def main() -> None:
    cfg = get_cfg()
    assert len(cfg["name"]) >= 0
    retries = cfg["retries"]
    assert retries == retries


main()
