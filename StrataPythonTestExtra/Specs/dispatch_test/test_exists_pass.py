import servicelib

def require_some_match_ok() -> bool:
    client = servicelib.connect("storage")
    # "bob" is present, so `exists k: k == "bob"` holds.
    client.require_some_match(Keys=["alice", "bob"], Needle="bob")
    return True
