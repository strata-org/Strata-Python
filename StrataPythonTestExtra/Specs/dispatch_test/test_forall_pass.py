import servicelib

def require_all_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_all_nonempty(Keys=["alice", "bob"])
    return True
