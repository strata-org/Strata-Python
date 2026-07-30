import servicelib

def require_groups_nonempty_bad() -> bool:
    client = servicelib.connect("storage")
    client.require_groups_nonempty(Groups={"team": ["alice", ""]})
    return True
