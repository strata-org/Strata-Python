import servicelib

def require_some_value_match_ok() -> bool:
    client = servicelib.connect("storage")
    # The value at "bob" is "y", so `exists k: d[k] == "y"` holds.
    client.require_some_value_match(Items={"alice": "x", "bob": "y"}, Needle="y")
    return True
