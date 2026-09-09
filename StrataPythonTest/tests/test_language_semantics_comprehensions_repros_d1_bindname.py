# repro.py, DESUGARED: bind the subscript to a NAME before iterating.
from typing import TypedDict, List

class App(TypedDict):
    appId: int

class AppsResponse(TypedDict):
    apps: List[App]

def list_apps() -> AppsResponse:
    return {"apps": [{"appId": 1}, {"appId": 2}]}

def main() -> None:
    resp = list_apps()
    apps = resp['apps']                  # <-- intermediate binding
    ids = [a['appId'] for a in apps]     # iterable is now a NAME
    assert len(ids) == len(apps)
main()
