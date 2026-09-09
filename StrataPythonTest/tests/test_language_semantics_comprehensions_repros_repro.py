# Repro
from typing import TypedDict, List


class App(TypedDict):
    appId: str


class ListAppsResponse(TypedDict):
    apps: List[App]


def list_apps() -> ListAppsResponse:
    return {"apps": [{"appId": "a"}, {"appId": "b"}]}


def main() -> None:
    resp = list_apps()
    ids = [app['appId'] for app in resp['apps']]   # <-- lowered to a while loop
    assert len(ids) == len(resp['apps'])


main()
