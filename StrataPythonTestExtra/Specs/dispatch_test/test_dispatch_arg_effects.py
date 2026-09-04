import servicelib
from servicelib.Contract import modeled_text


def connect_with_effectful_arg(flag: bool) -> bool:
    client = servicelib.connect("storage", label=modeled_text("x") if flag else "y")
    client.put_item(Bucket="b", Key="k", Data="d")
    return True
