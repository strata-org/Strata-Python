import servicelib

def require_shadowed_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_shadowed_nonempty(Keys=["alice", ""])
    return True
