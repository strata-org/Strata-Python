# Negative pair: an identity comprehension cannot change the source length.
from typing import List, TypedDict


class App(TypedDict):
    appId: int


class AppsResponse(TypedDict):
    apps: List[App]


def list_apps() -> AppsResponse:
    return {"apps": [{"appId": 1}, {"appId": 2}]}


def main() -> None:
    apps = list_apps()["apps"]
    ids = [app["appId"] for app in apps]
    assert len(ids) == len(apps) + 1


main()
