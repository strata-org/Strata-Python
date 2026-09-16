from typing import Any

import servicelib


def gradual_any_violation() -> bool:
    client = servicelib.connect("storage")
    item: Any = "not-a-dict"
    client.require_named_item(item)
    return True
