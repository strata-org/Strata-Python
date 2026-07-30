import servicelib

def require_groups_nonempty_ok() -> bool:
    client = servicelib.connect("storage")
    client.require_groups_nonempty(Groups={"team": ["alice", "bob"]})
    return True
