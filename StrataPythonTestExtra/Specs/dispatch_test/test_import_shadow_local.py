from typing import Any

connect: Any = 42
from servicelib import connect


def use_it() -> bool:
    client = connect("storage")
    result = client.get_item(Bucket="b", Key="k")
    return True
