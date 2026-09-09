# Negative pair: a concrete list length cannot be negative.
from typing import List, TypedDict


class App(TypedDict):
    appId: str


class ListAppsResponse(TypedDict):
    apps: List[App]


def list_apps() -> ListAppsResponse:
    return {"apps": [{"appId": "a"}, {"appId": "b"}]}


def main() -> None:
    apps = list_apps()["apps"]
    assert len(apps) < 0


main()
