import servicelib

def require_keys_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_keys_nonempty(Items={"alice": "x", "bob": "y"})
    return True
