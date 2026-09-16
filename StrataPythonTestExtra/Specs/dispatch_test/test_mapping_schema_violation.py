from typing import Any

import servicelib


def mapping_schema_bad() -> bool:
    client = servicelib.connect("storage")
    params: dict[str, Any] = {
        "Bucket": "mybucket",
        "Key": "mykey",
        "Data": "payload",
        "Bogus": "unexpected",
    }
    client.put_item(**params)
    return True
