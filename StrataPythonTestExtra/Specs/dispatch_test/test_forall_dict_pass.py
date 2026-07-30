import servicelib

def require_map_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_map_nonempty(Items={"alice": "x", "bob": "y"})
    return True
