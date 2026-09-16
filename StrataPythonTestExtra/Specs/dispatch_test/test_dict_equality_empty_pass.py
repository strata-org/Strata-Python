import servicelib


def require_dict_equal_empty() -> bool:
    client = servicelib.connect("storage")
    client.require_dict_equal(Left={}, Right={})
    return True
