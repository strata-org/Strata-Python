# Does a TypedDict field read on a SYMBOLIC-length dict trip the fail-closed
# scan bound (python-model-bound) under --python-smt-containers?
# python_container_ops.cpp:96 caps every key lookup at PYTHON_MAX_DICT_SIZE (16).
from typing import TypedDict, List


class App(TypedDict):
    appId: str


class ListAppsResponse(TypedDict):
    apps: List[App]


def list_apps() -> ListAppsResponse:
    return {"apps": [{"appId": "a"}, {"appId": "b"}]}


def main() -> None:
    resp = list_apps()
    # a single field read on a stub-returned TypedDict
    apps = resp['apps']
    assert len(apps) >= 0


main()
