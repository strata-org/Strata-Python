import servicelib

def require_shadowed_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_shadowed_nonempty(Keys=["alice", "bob"])
    return True
