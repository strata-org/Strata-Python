import servicelib

def require_others_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    # "" is not the sentinel, so the guard does not exclude it: the contract must fail.
    client.require_others_nonempty(Keys=["alice", ""], Sentinel="bob")
    return True
