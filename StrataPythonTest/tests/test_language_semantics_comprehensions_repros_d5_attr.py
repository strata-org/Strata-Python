# Same field access, but via a CLASS ATTRIBUTE instead of a dict subscript.
from typing import List
class App:
    def __init__(self, appId: int) -> None:
        self.appId = appId
def list_apps() -> List[App]:
    return [App(1), App(2)]
def main() -> None:
    apps = list_apps()
    ids = [a.appId for a in apps]     # attribute, not subscript
    assert len(ids) == len(apps)
main()
