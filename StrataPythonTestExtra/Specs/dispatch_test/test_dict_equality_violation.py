import servicelib


def require_dict_equal_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_dict_equal(
        Left={"a": {"nested": 1}},
        Right={"a": {"nested": 2}})
    return True
