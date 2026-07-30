import servicelib

def require_map_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    # The value for "bob" is empty, violating `assert len(v) >= 1`.
    client.require_map_nonempty(Items={"alice": "x", "bob": ""})
    return True
