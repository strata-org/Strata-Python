# Negative pair: an absent optional key is read without a membership guard.
from typing import NotRequired, TypedDict


class Cfg(TypedDict):
    name: str
    retries: NotRequired[int]


def get_cfg() -> Cfg:
    return {"name": "worker"}


def main() -> None:
    retries = get_cfg()["retries"]
    assert retries == retries


main()
