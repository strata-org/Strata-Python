import servicelib

def require_all_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_all_nonempty(Keys=["alice", ""])
    return True
