# Negative pair: projection preserves the number of source elements.
from typing import List, TypedDict


class App(TypedDict):
    appId: str


class ListAppsResponse(TypedDict):
    apps: List[App]


def list_apps() -> ListAppsResponse:
    return {"apps": [{"appId": "a"}, {"appId": "b"}]}


def main() -> None:
    apps = list_apps()["apps"]
    ids = [app["appId"] for app in apps]
    assert len(ids) != len(apps)


main()
