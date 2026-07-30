import servicelib

def require_values_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_values_nonempty(Items={"alice": "x", "bob": "y"})
    return True
