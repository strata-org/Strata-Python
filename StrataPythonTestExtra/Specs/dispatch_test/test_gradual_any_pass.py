from typing import Any

import servicelib


def gradual_any_pass() -> bool:
    client = servicelib.connect("storage")
    item: Any = {"Name": "gradual"}
    client.require_named_item(item)
    return True
