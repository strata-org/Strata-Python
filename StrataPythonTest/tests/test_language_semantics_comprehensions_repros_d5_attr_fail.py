# Negative pair: attribute projection over a nonempty source is nonempty.
from typing import List


class App:
    def __init__(self, app_id: int) -> None:
        self.app_id = app_id


def list_apps() -> List[App]:
    return [App(1), App(2)]


def main() -> None:
    ids = [app.app_id for app in list_apps()]
    assert ids == []


main()
