from typing import Any

import servicelib


def typed_dict_width_pass() -> bool:
    client = servicelib.connect("storage")
    item: dict[str, Any] = {
        "Name": "item",
        "Extra": "allowed by structural width subtyping",
    }
    client.require_named_item(item)
    return True
