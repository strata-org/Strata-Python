# DESUGARING ATTEMPT: split [a['appId'] for a in apps] into two stages.
# Stage 1 extracts the field (still a subscript -> may-raise);
# Stage 2 is pure. If stage 1 alone is the blocker, this still hangs.
from typing import TypedDict, List

class App(TypedDict):
    appId: int

def list_apps() -> List[App]:
    return [{"appId": 1}, {"appId": 2}]

def main() -> None:
    apps = list_apps()
    raw = [a['appId'] for a in apps]    # STAGE 1: subscript element
    ids = [r + 0 for r in raw]          # STAGE 2: pure
    assert len(ids) == len(apps)
main()
