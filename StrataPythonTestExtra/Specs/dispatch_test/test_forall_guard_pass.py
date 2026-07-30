import servicelib

def require_others_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    # "" is present but equals the sentinel, so the k != Sentinel guard excludes it.
    client.require_others_nonempty(Keys=["alice", ""], Sentinel="")
    return True
