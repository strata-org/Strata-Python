import servicelib


def require_lookup_equal_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_lookup_equal(
        Items={"config": "not-a-dict"},
        Expected={})
    return True
