import servicelib
from typing import Any


def fetch_item() -> bool:
    client: Any = servicelib.connect("storage")
    result = client.get_item(Bucket="mybucket", Key="mykey")
    return True
