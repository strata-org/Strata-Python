import servicelib

def require_some_match_bad() -> bool:
    client = servicelib.connect("storage")
    # "carol" is absent, so `exists k: k == "carol"` does not hold.
    client.require_some_match(Keys=["alice", "bob"], Needle="carol")
    return True
