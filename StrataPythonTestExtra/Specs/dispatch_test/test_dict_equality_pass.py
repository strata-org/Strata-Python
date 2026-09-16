import servicelib


def require_dict_equal_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_dict_equal(
        Left={"group": {"alice": "x", "bob": "y"}},
        Right={"group": {"bob": "y", "alice": "x"}})
    return True
