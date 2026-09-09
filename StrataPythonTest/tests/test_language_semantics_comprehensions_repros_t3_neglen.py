# Is a stub-returned container's length constrained NON-NEGATIVE?
# `len(x) >= 0` is a tautology in Python -- len() cannot return a negative.
# If this FAILS, the model admits negative-length containers, which would make
# every downstream `0 <= j < len` quantifier vacuous on that path.
from typing import TypedDict, List


class App(TypedDict):
    appId: str


class ListAppsResponse(TypedDict):
    apps: List[App]


def list_apps() -> ListAppsResponse:
    return {"apps": [{"appId": "a"}, {"appId": "b"}]}


def main() -> None:
    resp = list_apps()
    apps = resp['apps']
    assert len(apps) >= 0, "len() is never negative"


main()
