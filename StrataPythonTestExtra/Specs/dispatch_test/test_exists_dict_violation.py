import servicelib

def require_some_value_match_bad() -> bool:
    client = servicelib.connect("storage")
    # No value equals "carol", so `exists k: d[k] == "carol"` does not hold.
    client.require_some_value_match(Items={"alice": "x", "bob": "y"}, Needle="carol")
    return True
