import servicelib


def require_lookup_equal_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_lookup_equal(
        Items={"config": {"alice": "x", "bob": "y"}},
        Expected={"bob": "y", "alice": "x"})
    return True
