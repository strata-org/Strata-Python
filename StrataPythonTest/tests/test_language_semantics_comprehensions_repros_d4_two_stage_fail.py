# Negative pair: neither mapping stage may invent an extra element.
from typing import List, TypedDict


class App(TypedDict):
    appId: int


def list_apps() -> List[App]:
    return [{"appId": 1}, {"appId": 2}]


def main() -> None:
    apps = list_apps()
    raw = [app["appId"] for app in apps]
    ids = [value + 0 for value in raw]
    assert len(ids) != len(apps)


main()
