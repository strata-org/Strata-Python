from typing import Any

import servicelib


def mapping_schema_ok() -> bool:
    client = servicelib.connect("storage")
    params: dict[str, Any] = {
        "Bucket": "mybucket",
        "Key": "mykey",
        "Data": "payload",
    }
    client.put_item(**params)
    return True
